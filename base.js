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

function quote_desugar(exp) {
    if (pairp(exp)) {
        return list(intern("cons"), quote_desugar(exp.cdr.car), quote_desugar(exp.cdr.cdr));
    } else if (exp == null) {
        return list(intern("quote"), null);
    }else if(constantp(exp)) {
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
        case intern("quote"): return quote_desugar(exp.cdr.car);
        case intern("quasiquote"): return quasiquote_desugar(exp.cdr.car);
        default: return cons(desugar(exp.car), desugar(exp.cdr));
        }
    } else {
        return exp;
    }
}

function lookup(x, xs) {
    while(xs != null) {
        if (x.string === xs.car.car.string) { return xs.car.cdr; }
        else { xs = xs.cdr; }
    } return false;
}

function frees(exp, env, fenv) {
    if(pairp(exp)) {
        switch(exp.car) {
        case intern("quote"): return exp;
        case intern("cons"):
           return cons(exp.car, map(function(x) { return frees(x, env, fenv); }, exp.cdr));
        case intern("=="):
            return cons(exp.car, map(function(x) { return frees(x, env, fenv); }, exp.cdr));
        case intern("begin"):
            return cons(exp.car, map(function(x) { return frees(x, env, fenv); }, exp.cdr));
        case intern("fresh"):
            var bindings = exp.cdr.car;
            var body = exp.cdr.cdr;
            var e1 = foldl(bindings, env, function(e, a) { return cons(cons(a, a), e); });
            return cons(exp.car, cons(bindings, map(function(x) { return frees(x, e1, fenv); }, body)));
        default: throw "unkown exp: " + exp;
        }
    } else if(constantp(exp)) {
        return exp;
    } else if(symbolp(exp)) {
        if (lookup(exp, env)) { return exp; }
        var v = lookup(exp, fenv.get());
        if (v) {
            return v;
        } else {
            var gen = gensym(exp.string);
            fenv.set(cons(cons(exp, gen), fenv.get()));
            return gen;
        }
    } else {
        throw "unkown exp: " + exp;
    }
}

// returns list(exp, env, s_c)
function lift_frees(exp) {
    var free_env = ref(null);
    var exp1 = frees(exp, null, free_env);
    var e1_c1 = foldl(free_env.get(), cons(null, 0),
                      function(e_c, a) { return cons(cons(cons(a.cdr, mkvar(e_c.cdr)), e_c.car), e_c.cdr+1); });
    return list(exp1, e1_c1.car, cons(null ,e1_c1.cdr));
} 

function eval(exp, env) {
    if(pairp(exp)) {
        switch(exp.car) {
        case intern("quote"): return exp.cdr.car;
        case intern("cons"): return cons(eval(exp.cdr.car, env), eval(exp.cdr.cdr.car, env));
        case intern("=="): return eqeq(eval(exp.cdr.car, env), eval(exp.cdr.cdr.car, env));
        case intern("begin"):
            if (exp.cdr == null) { throw "error: empty begin"; }
            else if (exp.cdr.cdr == null) { return eval(exp.cdr.car, env); }
            else { return conj(eval(exp.cdr.car, env), eval(cons(intern("begin"), exp.cdr.cdr), env)); }
        case intern("fresh"):
            var bindings = exp.cdr.car;
            var body = exp.cdr.cdr;
            return function(s_c) {
                var e1_c1 = foldl(bindings, cons(env, s_c.cdr),
                                  function(e_c, a) { return cons(cons(cons(a, mkvar(e_c.cdr)), e_c.car), e_c.cdr+1); });
                return eval(cons(intern("begin"), body), e1_c1.car)(cons(s_c.car, e1_c1.cdr));
            };
        default: throw "unkown exp: " + exp;
        }
    } else if(constantp(exp)) {
        return exp;
    } else if(symbolp(exp)) {
        var v = lookup(exp, env);
        if(v) { return v; } else { throw ["unbound variable: " + exp.string, env]; }
    } else {
        throw "unkown exp: " + exp;
    }
}

// query a variable form the store
// if it doesn't exist, return a pretty printed "any"
function query(v, s) {
    return assq(v, s).cdr || ["_", v.c].join(".");
}

function map_stream(fn, stream) {
    return function() {
        var $ = pull(stream);
        return ($ == null) ? null : cons(fn($.car), map_stream(fn, $.cdr));
    };
}

// take the starting state of the interpreter
// make a stream of each top-level variable queried from the result store
function query_stream(init) {
    var exp = init.car;
    var env = init.cdr.car;
    var s_c = init.cdr.cdr.car;
    var $ = eval(exp, env)(s_c);

    var run_queries = function(s_c) { 
        var s = s_c.car;
        var record = new Object(null);
        map(function(x) { record[x.car.string] = query(x.cdr,s); }, env);
        return record;
    };
    return map_stream(run_queries, $);
}

function stream_generator($) {
    var state;
    return function() { state = $(); return state.car; };
}

// TODO: multi-expression programs
function run_program(p) {
    var desugared = desugar(p);
    var lifted = lift_frees(desugared);
    var q$ = query_stream(lifted);
    return stream_generator(q$);
}
