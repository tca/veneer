
function pair(car, cdr) {
    this.car = car;
    this.cdr = cdr;
}
function cons(car,cdr) { return new pair(car,cdr); }

var symbol_table = new Object(null);

function Symbol(str) { this.string = str; }
function intern(string) {
    var sym = new Symbol(string);
    symbol_table[string] = sym;
    return sym;
}

function reverse(lst,memo) {
    while(lst != null) {
        memo = cons(lst.car, memo);
        lst = lst.cdr;
    } return memo;
}

var eof = ["eof"];
function eofp(c) { return eof === c; }

function Stream(string) {
    var length = string.length;
    this.pos = 0;
    this.line = 1;
    this.string = string;
    this.peek_char = function() {
        return (this.pos >= length) ? eof : string[this.pos];
    }
    this.read_char = function() {
        var old_pos = this.pos;
        this.pos++;
        //if (string[old_pos] == "\n") { line++; }
        return (old_pos >= length) ? eof : string[old_pos];
    }
    this.unread_char = function() {
        //if (string[this.pos-1] == "\n") { line--; }
        this.pos--;
    }
    this.fork = function() {
        var fork = new Stream(string);
        fork.pos = this.pos;
        fork.line = this.line;
        return fork;
    }
}

function condition(args) {
    this.resume = args.resume;
    this.msg = args.msg;
}

function whitespacep(c) { return /\s+/.test(c); }
function symbolicp(c) { return /[a-zA-Z0-9=\/\\!@#$%^&*_+=-?.~<>]/.test(c); }
function number_stringp(s) { return /^([0-9]*\.)?[0-9]+$/.test(s); }

function skip_whitespace(input_stream) {
    var c;
    while(true) {
        c = input_stream.read_char();
        if(!whitespacep(c)) { break; }
    }
    input_stream.unread_char();
}

function read_symbol(input_stream) {
    var buffer = [input_stream.read_char()];
    var c;
    while(true) {
        c = input_stream.read_char();
        if(!eofp(c) && symbolicp(c)) {
            buffer.push(c);
        } else {
            input_stream.unread_char();
            var result = buffer.join("");
            return (number_stringp(result) ? parseFloat(result) : intern(result));
        }
    }
}

function read_string(input_stream) {
    var buffer = [];
    var c;
    input_stream.read_char();
    while(c = input_stream.read_char()) {
        if(c == '"') {
            return buffer.join("");
        } else if (c == "\\") {
            buffer.push(input_stream.read_char());
        } else {
            buffer.push(c);
        }
    }
}

function read_after_whitespace(input_stream) {
    skip_whitespace(input_stream);
    return read(input_stream);
}

function read_after_comment(input_stream) {
    while(input_stream.read_char() != "\n") {}
    return read(input_stream);
}

function read_quoted(input_stream) {
    input_stream.read_char();
    return cons(intern("quote"), cons(read(input_stream), null));
}

function read_quasiquoted(input_stream) {
    input_stream.read_char();
    return cons(intern("quasiquote"), cons(read(input_stream), null));
}

function read_unquoted(input_stream) {
    input_stream.read_char();
    return cons(intern("unquote"), cons(read(input_stream), null));
}

function read_list(input_stream) {
    input_stream.read_char();
    return read_list_aux(null, input_stream);
}

function read_list_aux(sexps, input_stream) {
    while (true) {
        skip_whitespace(input_stream);
        var c = input_stream.peek_char();
        switch (c) {
        case eof:
            throw "unexpected eof";
        case ")":
            input_stream.read_char();
            return reverse(sexps, null);
        case ".":
            return read_after_dot(sexps, input_stream);
        default:
            sexps = cons(read(input_stream), sexps);
        }
    }
}

function read_after_dot(sexps, input_stream) {
    input_stream.read_char();
    var last = read(input_stream);
    skip_whitespace(input_stream);
    var c = input_stream.peek_char();
    switch (c) {
    case eof:
        throw "unexpected eof";
    case ")":
        input_stream.read_char();
        break;
    default:
        throw "too many expressions after dot";
    }
    return reverse(sexps, last);
}

function read_hash(input_stream) {
    input_stream.read_char();
    switch (input_stream.read_char()) {
    case "f": return false;
    case "t": return true;
    case "\\": return input_stream.read_char();
    default: throw { msg: "unknown hash code" };
    }
}

function reader_for(c) {
    switch(c) {
    case '"': return read_string;
    case "'": return read_quoted;
    case "`": return read_quasiquoted;
    case ",": return read_unquoted;
    case "(": return read_list;
    case ";": return read_comment;
    case "#": return read_hash;
    }
    if (whitespacep(c)) { return read_whitespace; }
    if (symbolicp(c)) { return read_symbol; }
    return false;
}

function read(input_stream) {
    var c = input_stream.peek_char();
    var reader = reader_for(c);
    if(reader) { return reader(input_stream); }
    throw "no reader for: " + c;
}

function read_top(sexps, input_stream) {
    while (true) {
        skip_whitespace(input_stream);
        var c = input_stream.peek_char();
        if (c === eof) {
            input_stream.read_char();
            return reverse(sexps, null);
        } else {
            sexps = cons(read(input_stream), sexps);
        }
    }
}

var read_repl = function(in_stream) { return read_top(null, new Stream(in_stream)); };

function read_whole_program(str) {
    try { return read_top(null, new Stream(str)); }
    catch(err) { return err.msg; }
}
