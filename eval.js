
function quote_desugar(exp) {
    if (pairp(exp)) {
        return list(intern("cons"), quote_desugar(exp.car), quote_desugar(exp.cdr));
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
            desugar(exp.cdr.car) :
            list(intern("cons"), quasiquote_desugar(exp.car), quasiquote_desugar(exp.cdr));
    } else {
        return desugar(list(intern("quote"), exp));
    }
}

function desugar(exp) {
    if(pairp(exp)) {
        switch(exp.car) {
        case intern("define"):
            if(pairp(exp.cdr.car)) {
                return list(exp.car, exp.cdr.car.car, cons(intern("lambda"), cons(exp.cdr.car.cdr, desugar(exp.cdr.cdr))));
            } else {
                return list(exp.car, exp.cdr.car, desugar(exp.cdr.cdr.car));
            }
        case intern("quote"): return quote_desugar(exp.cdr.car);
        case intern("quasiquote"): return quasiquote_desugar(exp.cdr.car);
        case intern("conde"):
            var clauses = map(function(row) { return cons(intern("conj"), row); }, exp.cdr);
            return desugar(cons(intern("disj"), clauses));
        default: return cons(desugar(exp.car), desugar(exp.cdr));
        }
    } else {
        return exp;
    }
}

function register_define(exp) {
    if (pairp(exp) && exp.car == intern("define")) {
        var a = pairp(exp.cdr.car) ? exp.cdr.car.car : exp.cdr.car;
        toplevel[a.string] = null;
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
        case intern("zzz"):
            return list(exp.car, frees(exp.cdr.car, env, fenv));
        case intern("define"):
            var a = exp.cdr.car;
            toplevel[a.string] = null;
            return list(exp.car, exp.cdr.car, frees(exp.cdr.cdr.car, cons(cons(a, a), null), null));
        case intern("quote"): return exp;
        case intern("cons"):
            return cons(exp.car, map(function(x) { return frees(x, env, fenv); }, exp.cdr));
        case intern("=="):
            return cons(exp.car, map(function(x) { return frees(x, env, fenv); }, exp.cdr));
        case intern("=/="):
            return cons(exp.car, map(function(x) { return frees(x, env, fenv); }, exp.cdr));
        case intern("symbolo"):
            return cons(exp.car, map(function(x) { return frees(x, env, fenv); }, exp.cdr));
        case intern("numbero"):
            return cons(exp.car, map(function(x) { return frees(x, env, fenv); }, exp.cdr));
        case intern("conj"):
            return cons(exp.car, map(function(x) { return frees(x, env, fenv); }, exp.cdr));
        case intern("disj"):
            return cons(exp.car, map(function(x) { return frees(x, env, fenv); }, exp.cdr));
        case intern("lambda"):
            var bindings = exp.cdr.car;
            var body = exp.cdr.cdr;
            var e1 = foldl(bindings, env, function(e, a) { return cons(cons(a, a), e); });
            return cons(exp.car, cons(bindings, map(function(x) { return frees(x, e1, fenv); }, body)));
        case intern("fresh"):
            var bindings = exp.cdr.car;
            var body = exp.cdr.cdr;
            var e1 = foldl(bindings, env, function(e, a) { return cons(cons(a, a), e); });
            return cons(exp.car, cons(bindings, map(function(x) { return frees(x, e1, fenv); }, body)));
        default:
            return map(function(x) { return frees(x, env, fenv); }, exp);
        }
    } else if(constantp(exp)) {
        return exp;
    } else if(symbolp(exp)) {
        if (lookup(exp, env) || toplevel.hasOwnProperty(exp.string)) { return exp; }
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



// instead of returning a value, it returns a function that fetches a value
// based on the offset of how far it takes to reach the variable
// values in the env are expected to be :: offset -> cenv -> value
function lookup_calc(x, xs) {
    var n = 0;
    while(xs != null) {
        if (x.string === xs.car.car.string) { return xs.car.cdr(n); }
        else { n++; xs = xs.cdr; }
    } return false;
}
function augment_env(env, name) {
    var binding = cons(name, function (offset) { return function(cenv) { return cenv[offset]; } });
    return cons(binding, env);
}

function lift_frees(exp) {
    var free_env = ref(null);
    var exp1 = frees(exp, null, free_env);
    var e1_c1 = foldl(free_env.get(), cons(null, 0),
                      function(e_c, a) {
                          var var1 = mkvar(e_c.cdr);
                          var retrieve = function(_) { return function(_) { return var1; }; };
                          return cons(cons(cons(a.cdr, retrieve), e_c.car), e_c.cdr+1); });
    return list(exp1, e1_c1.car, Mks(null ,e1_c1.cdr, null, null, null));
}

function eval0(exp, env) {
    if(pairp(exp)) {
        switch(exp.car) {
        case intern("zzz"):
            var x = eval0(exp.cdr.car, env);
            return function(cenv) { return function(mks) { return function() { return x(cenv)(mks); }; }; };
        case intern("define"):
            var result = eval0(exp.cdr.cdr.car, env);
            toplevel[exp.cdr.car.string] = result;
            return function(cenv) { return unit; };
        case intern("quote"):
            return function(cenv) { return exp.cdr.car; };
        case intern("cons"): 
            var e1 = eval0(exp.cdr.car, env);
            var e2 = eval0(exp.cdr.cdr.car, env);
            return function(cenv) { return cons(e1(cenv), e2(cenv)); };
        case intern("=="):
            var e1 = eval0(exp.cdr.car, env);
            var e2 = eval0(exp.cdr.cdr.car, env);
            return function(cenv) { return eqeq(e1(cenv), e2(cenv)); }
        case intern("=/="):
            var e1 = eval0(exp.cdr.car, env);
            var e2 = eval0(exp.cdr.cdr.car, env);
            return function(cenv) { return noteqeq(e1(cenv), e2(cenv)); }
        case intern("symbolo"):
            var e1 = eval0(exp.cdr.car, env);
            return function(cenv) { return symbolo(e1(cenv)); }
        case intern("numbero"):
            var e1 = eval0(exp.cdr.car, env);
            return function(cenv) { return numbero(e1(cenv)); }
        case intern("conj"):
            if (exp.cdr == null) { throw "error: empty conj"; }
            else if (exp.cdr.cdr == null) {
                var e1 = eval0(list(intern("zzz"), exp.cdr.car), env);
                return e1;
            } else {
                var e1 = eval0(list(intern("zzz"), exp.cdr.car), env);
                var e2 = eval0(cons(intern("conj"), exp.cdr.cdr), env);
                return function(cenv) { return conj(e1(cenv), e2(cenv)); };
            }
        case intern("disj"):
            if (exp.cdr == null) { throw "error: empty conj"; }
            else if (exp.cdr.cdr == null) {
                var e1 = eval0(list(intern("zzz"), exp.cdr.car), env);
                return e1;
            } else {
                var e1 = eval0(list(intern("zzz"), exp.cdr.car), env);
                var e2 = eval0(cons(intern("disj"), exp.cdr.cdr), env);
                return function(cenv) { return disj(e1(cenv), e2(cenv)); };
            }
        case intern("fresh"):
            var bindings = reverse(exp.cdr.car);
            var body = exp.cdr.cdr;
            var env1 = foldl(bindings, env, augment_env);
            var body1 = eval0(cons(intern("conj"), body), env1);
            var arglen = length(bindings);

            return function (cenv) {
                return function(mks) {
                    var args1 = new Array(arglen);
                    var i = 0;

                    var c1 = foldl(bindings, mks.counter, function(c, a) {
                        args1[i++] = mkvar(c);
                        return c+1;
                    });

                    return body1(args1.concat(cenv))(Mks(mks.substitution, c1, mks.diseq, mks.symbols, mks.numbers));
                };
            };
        case intern("lambda"):
            var bindings = reverse(exp.cdr.car);
            var body = exp.cdr.cdr;

            var env1 = foldl(bindings, env, augment_env);
            var body1 = eval0(cons(intern("conj"), body), env1);

            return body1;
        default: // application
            var clos = eval0(exp.car, env);
            var args = map(function(e) { return eval0(e, env); }, exp.cdr);
            var arglen = length(args);
            return function(cenv) {
                var args1 = new Array(arglen);
                var i = 0;
                map(function(a) { args1[i++] = a(cenv); }, args);
                
                return clos(args1.concat(cenv));
            };
        }
    } else if(constantp(exp)) {
        return function(cenv) { return exp; };
    } else if(symbolp(exp)) {
        var v = lookup_calc(exp, env);
        if (v) {
            return v;
        } else if(toplevel.hasOwnProperty(exp.string)) {
            var mbox = ref(function() {
                var cache = toplevel[exp.string];
                mbox.set(function() { return cache; });
                return cache;
            });
            return function(cenv) {
                var val = mbox.get()();
                return val(cenv); };
        } else {
            throw ["unbound variable: " + exp.string, env];
        }
    } else {
        throw "unkown exp: " + exp;
    }
}


function query(v, s) {
    var v1 = walk_star(v, s);
    return walk_star(v1, reify_s(v1, null));
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
    var mks = init.cdr.cdr.car;
    var foo = eval0(exp, env)([]);
    var $ = foo(mks);

    var run_queries = function(mks) {
        var s = mks.substitution;
        var record = [];
        map(function(x) {
            record.push([x.car.string, ": ", pretty_print(query(x.cdr()(),s))].join(""));
        }, env);
        return record.join("\n");
    };
    return map_stream(run_queries, $);
}

function stream_generator($) {
    var next = $;
    return function() {
        var cur = next();
        if(cur == null) { return null; }
        else { next = cur.cdr;
               return cur.car; }
    };
}

var toplevel = new Object(null);
var vm_state = cons(null, mzero);

function run_expression(p) {
    var desugared = desugar(p);
    var lifted = lift_frees(desugared);
    var q$ = query_stream(lifted);
    return stream_generator(q$);
}

function run_program(p) {
    var stream;
    if(p == null) { throw "no program" }
    map(register_define, p);
    while(p != null) {
        stream = run_expression(p.car);
        p = p.cdr;
    } return stream;
}
