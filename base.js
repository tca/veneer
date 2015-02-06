function Pair(car, cdr) {
    this.car = car;
    this.cdr = cdr;
}
function car(x) { return x.car; }
function cdr(x) { return x.cdr; }
function pairp(x) { return x instanceof Pair }
function cons(car,cdr) { return new Pair(car,cdr); }


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
function numberp(t) { return typeof t == 'number'; }
function booleanp(t) { return typeof t == 'boolean'; }
function stringp(t) { return typeof t == 'string'}
function constantp(t)  { return numberp(t) || booleanp(t) || stringp(t); }

function Ref(v) {
    this.get = function() { return v; };
    this.set = function(v1) { v = v1; };
}

function ref(v) { return new Ref(v); }

function assp(pred, xs) {
    while(true) {
        if(xs == null) { return false; }
        else if (pred(xs.car)) { return xs.car; }
        else { xs = xs.cdr; }
    }
}

function reverse_aux(lst,memo) {
    while(lst != null) {
        memo = cons(lst.car, memo);
        lst = lst.cdr;
    } return memo;
}

function reverse(lst) {
    return reverse_aux(lst,null);
}

function array_to_list(arr) {
    var i = arr.length;
    var memo = null;
    while(i > 0) { memo = cons(arr[--i], memo); }
    return memo;
}

function map(fn, lst) {
    var memo = [];
    while(lst != null) {
        memo.push(fn(lst.car));
        lst = lst.cdr;
    } return array_to_list(memo);
}

function list() {
    return array_to_list(arguments);
}

function foldl(xs, m, fn) {
    while(xs != null) {
        m = fn(m, xs.car);
        xs = xs.cdr;
    } return m;
}

function assq(x, xs) {
    while(xs != null) {
        if (x === xs.car.car) { return xs.car; }
        else { xs = xs.cdr; }
    } return false;
}
