function Pair(car, cdr) {
    this.car = car;
    this.cdr = cdr;
}
function car(x) { return x.car; }
function cdr(x) { return x.cdr; }
function pairp(x) { return x instanceof Pair; }
function cons(car, cdr) { return new Pair(car, cdr); }


function Symbol(str) { this.string = str; }

function gensym(str) { return new Symbol(str); }

var symbol_table = new Object(null);
function intern(string) {
    if (symbol_table.hasOwnProperty(string)) {
        return symbol_table[string];
    } else {
        var sym = new Symbol(string);
        symbol_table[string] = sym;
        return sym;
    }
}

function procedurep(x) { return x instanceof Function; }
function symbolp(x) { return x instanceof Symbol; }
function numberp(t) { return typeof t === "number"; }
function booleanp(t) { return typeof t === "boolean"; }
function stringp(t) { return typeof t === "string"; }
function constantp(t) { return numberp(t) || booleanp(t) || stringp(t); }

function Ref(v) {
    this.val = v;
}
Ref.prototype.get = function() { return this.val; };
Ref.prototype.set = function(v1) { this.val = v1; };

function ref(v) { return new Ref(v); }

function anyp(pred, xs) {
    while(xs !== null) {
        if (pred(xs.car)) { return xs.car; }
        else { xs = xs.cdr; }
    } return false;
}

function memq(x, xs) {
    return anyp(function(y) { return x === y; }, xs);
}

function assp(pred, xs) {
    while(xs !== null) {
        if (pred(xs.car.car)) { return xs.car; }
        else { xs = xs.cdr; }
    } return false;
}

function length(lst) {
    var memo = 0;
    while(lst !== null) { memo++; lst = lst.cdr; }
    return memo;
}

function nth(xs, n) {
    while(--n > 0) { xs = xs.cdr; }
    return xs.car;
}

function reverse_aux(lst, memo) {
    while(lst !== null) {
        memo = cons(lst.car, memo);
        lst = lst.cdr;
    } return memo;
}

function reverse(lst) {
    return reverse_aux(lst, null);
}

function array_to_list(arr) {
    var i = arr.length;
    var memo = null;
    while(i > 0) { memo = cons(arr[--i], memo); }
    return memo;
}

function map(fn, lst) {
    var memo = [];
    while(lst !== null) {
        memo.push(fn(lst.car));
        lst = lst.cdr;
    } return array_to_list(memo);
}

function list() {
    return array_to_list(arguments);
}

function foldl(xs, m, fn) {
    while(xs !== null) {
        m = fn(m, xs.car);
        xs = xs.cdr;
    } return m;
}

function foldr(xs, m, fn) {
    return (xs === null) ? m : fn(xs.car, foldr(xs.cdr, m, fn));
}

function assq(x, xs) {
    while(xs !== null) {
        if (x === xs.car.car) { return xs.car; }
        else { xs = xs.cdr; }
    } return false;
}

function pretty_print(x) {
    if (numberp(x)) {
        return x.toString();
    } else if (x === null) {
        return "()";
    } else if (typeof x === "string") {
        return ["\"", x, "\""].join("");
    } else if (symbolp(x)) {
        return x.string;
    } else if (pairp(x)) {
        var cur = x;
        var memo = [];
        while(true) {
            if(pairp(cur.cdr)) {
                memo.push(pretty_print(cur.car));
                cur = cur.cdr;
            } else if (cur.cdr === null) {
                memo.push(pretty_print(cur.car));
                break;
            } else {
                memo.push(pretty_print(cur.car));
                memo.push(".");
                memo.push(pretty_print(cur.cdr));
                break;
            }
        } return ["(", memo.join(" "), ")"].join("");
    } else if (x && x.toString && typeof x.toString === "function") {
        return x.toString();
    } else {
        return JSON.stringify(x);
    }
}
