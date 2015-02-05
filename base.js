function Pair(car, cdr) {
    this.car = car;
    this.cdr = cdr;
}
function pairp(x) { return x instanceof Pair }
function cons(car,cdr) { return new Pair(car,cdr); }

function procedurep(x) { return x instanceof Function; }

var symbol_table = new Object(null);

function Symbol(str) { this.string = str; }
function intern(string) {
    var sym = new Symbol(string);
    symbol_table[string] = sym;
    return sym;
}
