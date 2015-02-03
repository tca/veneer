// todo: add parse result type so any reader can error
//       for example if it hits an unexpected eof

var eof = ["eof"];
function eofp(c) { return eof === c; }

// todo: make all uses of read_char and peek_char match cases for
//       eof | char of string
function stream(string) {
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
        var fork = new stream(string);
        fork.pos = this.pos;
        fork.line = this.line;
        return fork;
    }
}

function dotp(c) { return c == "."; }
function whitespacep(c) { return /\s+/.test(c); }
function symbolicp(c) { return /[a-zA-Z0-9=\/\\!@#$%^&*_+=-?.~<>]/.test(c); }
function number_stringp(cs) { return /[0-9]+/.test(cs.join("")); }

function skip_whitespace(input_stream) {
    var c;
    while(true) {
        c = input_stream.read_char();
        if(!whitespacep(c)) { break; }
    }
    input_stream.unread_char();
}

// intern symbol using table and [] for fresh
function read_symbol(input_stream) {
    var buffer = [input_stream.read_char()];
    var c;
    while(true) {
        c = input_stream.read_char();
        if(!eofp(c) && symbolicp(c)) {
            buffer.push(c);
        } else {
            input_stream.unread_char();
            return buffer.join("");
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

// todo: don't automatically read next
function read_whitespace(input_stream) {
    skip_whitespace(input_stream);
    return read(input_stream);
}

function read_until_end_of_line(input_stream) {
    while(input_stream.read_char() != "\n") {}
}

// todo: don't automatically read next
function read_comment(input_stream) {
    read_until_end_of_line(input_stream);
    return read(input_stream);
}

// todo: intern quote
function read_quoted(input_stream) {
    input_stream.read_char();
    return ["quote", read(input_stream)];
}

// todo: intern quasiquote
function read_quasiquoted(input_stream) {
    input_stream.read_char();
    return ["quasiquote", read(input_stream)];
}

// todo: intern unquote
function read_unquoted(input_stream) {
    input_stream.read_char();
    return ["unquote", read(input_stream)];
}

function read_list(input_stream) {
    input_stream.read_char();
    return read_list_aux([], input_stream);
}

function read_list_aux(sexps, input_stream) {
   skip_whitespace(input_stream);
    var c = input_stream.peek_char();
    if (eofp(c)) {
        throw "unexpected eof" // partial result
    } else if (c == ")") {
        input_stream.read_char();
        return sexps;
    } else if (dotp(input_stream.peek_char())) {
        input_stream.read_char();
        var result = sexps.concat(read(input_stream));
        skip_whitespace(input_stream);
        var c = input_stream.peek_char();
        if (c == ")") {
            input_stream.read_char();
        } else if (eofp(c)){
            throw "unexpected eof"
        } else {
            throw "stuff after dot";
        }
        return result;
    } else {
        skip_whitespace(input_stream);
        return read_list_aux(sexps.concat([read(input_stream)]), input_stream);
    }
}

function read_hash(input_stream) {
    input_stream.read_char();
    switch (input_stream.read_char()) {
    case "f": return false;
    case "t": return true;
    case "\\": return input_stream.read_char();
    default: throw "unknown hash code";
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

// todo: use option type, make sure all uses of read match it
function read(input_stream) {
    var c = input_stream.peek_char();
    var reader = reader_for(c);
    if(reader) { return reader(input_stream); }
    throw "no reader for: " + c;
}

// todo: use conses instead of arrays
//       loop for recursive case instead of recursion
function read_all(sexps, input_stream, t) {
    skip_whitespace(input_stream);
    var c = input_stream.peek_char();
    if (eofp(c)) {
        input_stream.read_char();
        return sexps;
    } else {
        skip_whitespace(input_stream);
        return read_all(sexps.concat([read(input_stream)]), input_stream, t);
    }
}


function read_string(str) {
    try {
        return read_all([], new stream(str), true)
    }
    catch(err) {
        return err;
    }
}
