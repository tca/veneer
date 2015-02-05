function Pair(car, cdr) {
    this.car = car;
    this.cdr = cdr;
}
function car(x) { return x.car; }
function cdr(x) { return x.cdr; }
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
function symbolp(x) { return x instanceof Symbol; }
function numberp(t) { return typeof t == 'number'; }
function booleanp(t) { return typeof t == 'boolean'; }
function stringp(t) { return typeof t == 'string'}
function constantp(t)  { return numberp(t) || booleanp(t) || stringp(t); }

function assq(x, xs) {
    while(true) {
        if(xs == null) { return false; }
        else if (x === xs.car) { return xs.car; }
        else { xs = xs.cdr; }
    }
}

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

function map(fn, lst) {
    var memo = [];
    while(lst != null) {
        memo = memo.push(fn(lst.car));
        lst = lst.cdr;
    } return array_to_list(memo);
}

function array_to_list(arr) {
    var i = arr.length;
    var memo = null;
    while(i > 0) { memo = cons(arr[--i], memo); }
    return memo;
}

function list() {
    return array_to_list(arguments);
}

function quote_desugar(exp) {
    if (pairp(exp)) {
        return list(intern("cons"), quote_desugar(exp.car), quote_desugar(exp.cdr)) ;
    } else if(constantp(exp)) {
        return exp;
    } else {
        return list(intern("quote"), exp);
    }
}

function quasiquote_desugar(exp) {
    if (pairp(exp)) {
        return exp.car === intern("unquote") ?
            desugar(exp.cdr) :
            list(intern("cons"), quasiquote_desugar(exp.car), quasiquote_desugar(exp.cdr));
    } else {
        return desugar(list(intern("quote"), exp));
    }
}

function desugar(exp) {
    if(pairp(exp)) {
        switch(exp.car) {
        case intern("quote"): return quote_desugar(exp);
        case intern("quasiquote"): return quasiquote_desugar(exp);
        default: return cons(desugar(exp.car), desugar(exp.cdr));
        }
    } else {
        return exp;
    }
}

function foldl(xs, m, fn) {
    while(xs != null) {
        m = fn(m, xs.car);
        xs = xs.cdr;
    } return m;
}

function eval(exp, env, s_c) {
    if(pairp(exp)) {
        switch(exp.car) {
        case intern("quote"): return exp.cdr.car;
        case intern("cons"): return cons(exp.cdr.car, exp.cdr.cdr.car);
        case intern("=="): return eqeq(eval(exp.cdr.car, env, s_c), eval(exp.cdr.cdr.car, env, s_c));
        case intern("begin"):
            if (exp.cdr == null) { throw "error: empty begin"; }
            else if (exp.cdr.cdr == null) { return eval(exp.cdr.car, env, s_c); }
            else { return conj(eval(exp.cdr.car, env, s_c), eval(cons(intern("begin"), exp.cdr.cdr), env, s_c)); }
        case intern("fresh"):
            var bindings = exp.cdr.car;
            var body = exp.cdr.cdr;
            var e1_c1 = foldl(bindings, cons(env, s_c.cdr),
                              function(e_c, a) { return cons(cons(cons(a, mkvar(e_c.cdr)), e_c.car), e_c.cdr+1); });
            return eval(cons(intern("begin"), body), e1_c1.car, cons(s_c.car, e1_c1.cdr));
        default: throw "unkown exp: " + exp;
        }
    } else if(constanp(exp)) {
        return exp;
    } else if(symbolp(exp)) {
        var v = assq(exp, env);
        if(v) { return v; } else { throw "unbound variable: " + exp.string; }
    } else {
        throw "unkown exp: " + exp;
    }
}
