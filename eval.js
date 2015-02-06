
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
    var next = $;
    return function() {
        var cur = next();
        if(cur == null) { return null }
        else { next = cur.cdr;
               return cur.car; }
    };
}

// TODO: multi-expression programs
function run_program(p) {
    var desugared = desugar(p);
    var lifted = lift_frees(desugared);
    var q$ = query_stream(lifted);
    return stream_generator(q$);
}
