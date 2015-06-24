var runtime = require('./base');

var Pair = runtime.Pair;
var car = runtime.car;
var cdr = runtime.cdr;
var pairp = runtime.pairp;
var cons = runtime.cons;
var Symbol = runtime.Symbol;
var gensym = runtime.gensym;
var intern = runtime.intern;
var nullp = runtime.nullp;
var procedurep = runtime.procedurep;
var symbolp = runtime.symbolp;
var numberp = runtime.numberp;
var booleanp = runtime.booleanp;
var stringp = runtime.stringp;
var constantp = runtime.constantp;
var Ref = runtime.Ref;
var ref = runtime.ref;
var anyp = runtime.anyp;
var memq = runtime.memq;
var assp = runtime.assp;
var length = runtime.length;
var nth = runtime.nth;
var reverse_aux = runtime.reverse_aux;
var reverse = runtime.reverse;
var array_slice_list = runtime.array_slice_list;
var array_to_list = runtime.array_to_list;
var map = runtime.map;
var list = runtime.list;
var foldl = runtime.foldl;
var foldr = runtime.foldr;
var assq = runtime.assq;
var pretty_print = runtime.pretty_print;

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
        if (string[old_pos] == "\n") { this.line++; }
        return (old_pos >= length) ? eof : string[old_pos];
    }
    this.unread_char = function() {
        if (string[this.pos-1] == "\n") { this.line--; }
        this.pos--;
    }
}

function whitespacep(c) { return /\s+/.test(c); }
function symbolicp(c) { return /[a-zA-Z0-9=\/\\!@#$%^&*_+=\-?.~<>\:]/.test(c); }
function number_stringp(s) { return /^([0-9]*\.)?[0-9]+$/.test(s); }

function skip_whitespace(input_stream) {
    var c;
    while(true) {
        c = input_stream.read_char();
        if(!whitespacep(c)) { break; }
    }
    input_stream.unread_char();
}

function skip_whitespace_and_comments(input_stream) {
    var c;
    while(true) {
        c = input_stream.read_char();
        if(c == ";") {
            while(!eofp(c)) {
                c = input_stream.read_char();
                if(c == "\n") {
                    break;
                }
            }
        }
        else if(!whitespacep(c)) { break; }
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
    var c;
    while(true) {
        c = input_stream.read_char();
        if(c == "\n") {  return read(input_stream); }
        else if (c === eof) { throw "eof"; }
    }
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
        skip_whitespace_and_comments(input_stream);
        var c = input_stream.peek_char();
        switch (c) {
        case eof:
            throw "unexpected eof";
        case ")":
            input_stream.read_char();
            return reverse_aux(sexps, null);
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
    return reverse_aux(sexps, last);
}

function read_hash(input_stream) {
    input_stream.read_char();
    switch (input_stream.read_char()) {
    case "f": return false;
    case "t": return true;
    case "\\": return input_stream.read_char();
    default: throw  "unknown hash code";
    }
}

var readtable = {
    '"': read_string,
    "'": read_quoted,
    "`": read_quasiquoted,
    ",": read_unquoted,
    "(": read_list,
    ";": read_after_comment,
    "#": read_hash
    //eof: function(input_stream) { throw eof }
};

function reader_for(c) {
    var reader = readtable[c];
    if (reader) { return reader; }
    if (whitespacep(c)) { return read_after_whitespace; }
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
        skip_whitespace_and_comments(input_stream);
        var c = input_stream.peek_char();
        if (c === eof) {
            input_stream.read_char();
            return reverse_aux(sexps, null);
        } else {
            sexps = cons(read(input_stream), sexps);
        }
    }
}

function ReaderError(msg) { this.msg = msg; }
function read_program(str) {
    try { return read_top(null, new Stream(str)); }
    catch(err) { throw new ReaderError(err); }
}
exports = module.exports = read_program;
exports.Stream = Stream;
exports.ReaderError = ReaderError;
exports.read = read;
exports.reader_for = reader_for;
exports.readtable = readtable;
