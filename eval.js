function VeneerVM() {
    var toplevel = new Object(null);

    function register_define(exp) {
        if (pairp(exp) && exp.car === intern("define")) {
            var a = pairp(exp.cdr.car) ? exp.cdr.car.car : exp.cdr.car;
            toplevel[a.string] = null;
        }
    }

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

    function quasiquote_desugar(exp, n, env) {
        if (pairp(exp)) {
            if (exp.car === intern("unquote")) {
                if (n === 1) {
                    return desugar(exp.cdr.car, env);
                } else {
                    return list(intern("list"), list(intern("quote"), intern("unquote")),
                                quasiquote_desugar(exp.cdr.car, n - 1, env));
                }
            } else if (exp.car === intern("quasiquote")) {
                return  list(intern("list"), list(intern("quote"), intern("quasiquote")),
                             quasiquote_desugar(exp.cdr.car, n + 1, env));
            } else {
                return list(intern("cons"), quasiquote_desugar(exp.car, n, env),
                            quasiquote_desugar(exp.cdr, n, env));
            }
        } else {
            return quote_desugar(exp);
        }
    }

    function desugar(exp, env) {
        if(pairp(exp)) {
            // application
            var app = false;
            if(symbolp(exp.car)) {
                if(lookup(exp.car, env) || toplevel.hasOwnProperty(exp.car.string)) {
                    app = true;
                }
            } else if (pairp(exp.car)) {
                app = true;
            }
            if(app) {
                var fn = desugar(exp.car, env);
                var args = map(function(e) { return desugar(e, env); }, exp.cdr);
                var exp1 = cons(fn, args);
                return exp1;
            }
            // special forms & builtins
            switch(exp.car) {
            case intern("define"):
                if(pairp(exp.cdr.car)) {
                    // (define (x y z) f) => (define x (lambda (y z) f))
                    var name = exp.cdr.car.car;
                    var args = exp.cdr.car.cdr;
                    var body = exp.cdr.cdr;
                    var fn = cons(intern("lambda"), cons(args, body));
                    return list(exp.car, name,  desugar(fn, env));
                } else {
                    return list(exp.car, exp.cdr.car, desugar(exp.cdr.cdr.car, env));
                }
            case intern("quote"):
                return quote_desugar(exp.cdr.car);
            case intern("quasiquote"):
                return quasiquote_desugar(exp.cdr.car, 1, env);
            case intern("zzz"):
                return list(exp.car, desugar(exp.cdr.car, env));
            case intern("conde"):
                var clauses = map(function(row) { return cons(intern("conj"), row); }, exp.cdr);
                return desugar(cons(intern("disj"), clauses), env);
            case intern("conj"):
                if (exp.cdr == null) { throw "error: empty conj"; }
                else if (exp.cdr.cdr == null) {
                    var e1 = desugar(list(intern("zzz"), exp.cdr.car), env);
                    return e1;
                } else {
                    var e1 = list(intern("zzz"), exp.cdr.car);
                    var e2 = cons(intern("conj"), exp.cdr.cdr);
                    return desugar(list(intern("conj/2"), e1, e2), env);
                }
            case intern("disj"):
                if (exp.cdr == null) { throw "error: empty disj"; }
                else if (exp.cdr.cdr == null) {
                    var e1 = desugar(list(intern("zzz"), exp.cdr.car), env);
                    return e1;
                } else {
                    var e1 = list(intern("zzz"), exp.cdr.car);
                    var e2 = cons(intern("disj"), exp.cdr.cdr);
                    return desugar(list(intern("disj/2"), e1, e2), env);
                }
            case intern("begin"):
                return cons(exp.car, map(function(f) { return desugar(f, env); }, exp.cdr));
            case intern("fresh"):
                var bindings = exp.cdr.car;
                var body = exp.cdr.cdr;
                if (bindings === null) {
                    return desugar(cons(intern("conj"), body), env);
                } else {
                    var fn = list(intern("lambda"), bindings, cons(intern("conj"), body));
                    var body1 = desugar(fn, env);
                    var len = length(bindings);
                    return list(intern("apply/fresh-n"), len, body1);
                }
            case intern("lambda"):
                var bindings = exp.cdr.car;
                var body = exp.cdr.cdr;
                var env1 = foldl(bindings, env, augment_env);
                var body1 = desugar(cons(intern("begin"), body), env1);
                return list(exp.car, exp.cdr.car, body1);
            case intern("list"):
                return cons(exp.car, map(function(f) { return desugar(f, env); }, exp.cdr));
            default:
                if(builtins.hasOwnProperty(exp.car.string)) {
                    return cons(exp.car, map(function(f) { return desugar(f, env); }, exp.cdr));
                } else {
                    throw "unkown exp: " + pretty_print(exp);
                }
            }
        } else if(constantp(exp)) {
            return exp;
        } else if(symbolp(exp)) {
            return exp;
        } else {
            throw "unkown exp: " + pretty_print(exp);
        }
    }

    function lookup(x, xs) {
        while(xs !== null) {
            if (x === xs.car.car) { return xs.car.cdr; }
            else { xs = xs.cdr; }
        } return false;
    }

    function extend_boxed(env, a, v) {
        var envu = env.get();
        lookup(a, envu) || env.set(cons(cons(a, v), envu));
    }

    function frees(exp, env, lenv, fenv) {
        if(pairp(exp)) {
            switch(exp.car) {
            // special forms & macros
            case intern("define"):
                var a = exp.cdr.car;
                toplevel[a.string] = null;
                return list(exp.car, exp.cdr.car, frees(exp.cdr.cdr.car, list(cons(a, a)), list(a), null));
            case intern("quote"): return exp;
            case intern("lambda"):
                var bindings = exp.cdr.car;
                var body = exp.cdr.cdr;
                var e1 = foldl(bindings, env, function(e, a) { return cons(cons(a, a), e); });
                var inner_frees = ref(null);

                var re = cons(exp.car, cons(bindings, map(function(x) {
                    return frees(x, e1, bindings, inner_frees);
                }, body)));

                var proper_frees = null;
                map(function(v) {
                    if (!memq(v.car, bindings)) {
                        extend_boxed(fenv, v.car, v.cdr);
                        proper_frees = cons(v.cdr, proper_frees);
                    }
                }, inner_frees.get());

                re.frees = proper_frees;
                return re;
            // builtins
            case intern("begin"):
            case intern("zzz"):
            case intern("apply/fresh-n"):
                return cons(exp.car, map(function(x) { return frees(x, env, lenv, fenv); }, exp.cdr));
            default:
                return map(function(x) { return frees(x, env, lenv, fenv); }, exp);
            }
        } else if(constantp(exp)) {
            return exp;
        } else if(symbolp(exp)) {
            // bound variables, for now toplevel is included
            if (memq(exp, lenv) || toplevel.hasOwnProperty(exp.string)) { return exp; }
            if (lookup(exp, env)) { extend_boxed(fenv, exp, exp); return exp; }
            switch(exp) {
            // builtins
            case intern("list"):
                return exp;
            default: // free variables
                if (builtins.hasOwnProperty(exp.string)) {
                    return exp;
                } else if(fenv) {
                    var v = lookup(exp, fenv.get());
                    if (v) { return v; }
                    var gen = gensym(exp.string);
                    extend_boxed(fenv, exp, gen);
                    return gen;
                } else {
                    throw "unbound variable: " + exp.string;
                }
            }
        } else {
            throw "unkown exp: " + pretty_print(exp);
        }
    }

    // instead of returning a value, it returns a function that fetches a value
    // based on the offset of how far it takes to reach the variable
    // values in the env are expected to be :: offset -> cenv -> value
    function lookup_calc(x, xs) {
        var n = 0;
        while(xs !== null) {
            if (x === xs.car.car) { return xs.car.cdr(n); }
            else { n++; xs = xs.cdr; }
        } return false;
    }

    function augment_env(env, name) {
        var binding = cons(name, function (offset) { return function(cenv) { return cenv[offset]; }; });
        return cons(binding, env);
    }

    function lift_frees(exp) {
        var free_env = ref(null);
        var exp1 = frees(exp, null, null, free_env);
        var e1_c1 = foldl(free_env.get(), cons(null, 0),
                          function(e_c, a) {
                              var var1 = mkvar(e_c.cdr);
                              var retrieve = function(_) { return function(_) { return var1; }; };
                              return cons(cons(cons(a.cdr, retrieve), e_c.car), e_c.cdr + 1); });
        return list(exp1, e1_c1.car, Mks(Immutable.Map(), e1_c1.cdr, null, Immutable.Map(), null));
    }


    function eval0(exp, env) {
        if(pairp(exp)) {
            // application
            var clos = false;
            if(symbolp(exp.car)) {
                if(lookup(exp.car, env) || toplevel.hasOwnProperty(exp.car.string)) {
                    clos = eval0(exp.car, env);
                }
            } else if (pairp(exp.car)) {
                clos = eval0(exp.car, env);
            }

            if(clos) {
                var args = foldl(exp.cdr, null, function(m, e) {
                    return cons(eval0(e, env), m);
                });
                var len = length(args);
                return function(cenv) {
                    var clos1 = clos(cenv);
                    var fn = clos1.car;
                    var closure_env = clos1.cdr;
                    var new_env = build_env(len, args, cenv);
                    return fn(new_env.concat(closure_env));
                };
            }
            // special forms & builtins
            switch(exp.car) {
            case intern("define"):
                var result = eval0(exp.cdr.cdr.car, env);
                toplevel[exp.cdr.car.string] = result;
                return function(cenv) { return true; };
            case intern("quote"):
                var re = function(cenv) { return exp.cdr.car; };
                return re;
            case intern("zzz"):
                var e1 = eval0(exp.cdr.car, env);
                return function(cenv) { return function(mks) { return function() { return e1(cenv)(mks); }; }; };
            case intern("begin"):
                if (exp.cdr == null) { throw "error: empty begin"; }
                else if (exp.cdr.cdr == null) {
                    var e1 = eval0(exp.cdr.car, env);
                    return e1;
                } else {
                    var e1 = eval0(exp.cdr.car, env);
                    var e2 = eval0(cons(intern("begin"), exp.cdr.cdr), env);
                    return function(cenv) { e1(cenv); return e2(cenv); };
                }
            case intern("lambda"):
                var bindings = exp.cdr.car;
                var body = exp.cdr.cdr.car;
                var free_env = foldl(reverse(exp.frees), null, augment_env);
                var env1 = foldl(bindings, free_env, augment_env);
                var closure_env = map(function(v) { return eval0(v, env); }, exp.frees);
                var len = length(closure_env);
                var closure_env_build = function(cenv) {
                    return build_env(len, closure_env, cenv);
                };
                var body1 = eval0(body, env1);
                var closure = function(cenv) { return cons(body1, closure_env_build(cenv)); };
                return closure;
            case intern("apply/fresh-n"):
                var bindings = exp.cdr.car;
                var len = exp.cdr.car;
                var fn = exp.cdr.cdr.car;
                var closure = eval0(fn, env); 
                return function(cenv) {
                    var closure1 = closure(cenv);
                    var closure_env = closure1.cdr;
                    var closure_fn = closure1.car;
                    return function(mks) {
                        var c = mks.counter;
                        var e1_c1 = fresh_n(len, c);
                        var mks1 = Mks(mks.substitution, e1_c1[1], mks.diseq, mks.types, mks.absentee);
                        return closure_fn(e1_c1[0].concat(closure_env))(mks1);
                    };
                };
            case intern("list"):
                var args = map(function(e) { return eval0(e, env); }, exp.cdr);
                return function(cenv) {
                    return map(function(a) { return a(cenv); }, args);
                };
            default:
                if(builtins.hasOwnProperty(exp.car.string)) {
                    return builtins[exp.car.string](exp.cdr, env, eval0);
                } else {
                    throw "unkown exp: " + pretty_print(exp);
                }
            }
        } else if(constantp(exp)) {
            var re = function(cenv) { return exp; };
            return re;
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
                    return val(cenv);
                };
            } else {
                throw "unbound variable: " + pretty_print(exp);
            }
        } else {
            throw "unkown exp: " + pretty_print(exp);
        }
    }

    var builtins = new Object(null);
    builtins["cons"] = generate_fn_code("cons", 2);
    builtins["conj/2"] = generate_fn_code("conj", 2);
    builtins["disj/2"] = generate_fn_code("disj", 2);
    builtins["=="] = generate_fn_code("eqeq", 2);
    builtins["=/="] = generate_fn_code("noteqeq", 2);
    builtins["symbolo"] = generate_fn_code("symbolo", 1);
    builtins["numbero"] = generate_fn_code("numbero", 1);
    builtins["absento"] = generate_fn_code("absento", 2);
    builtins["build-num"] = generate_fn_code("build_num", 1);

    function generate_fn_code(name, arity) {
        var c = 0;
        var evalers = [];
        var callers = [];

        for(c = 0; c < arity; c++) {
            evalers = evalers.concat(["var e", c, " = eval0(nth(args, ", c+1, "), env);\n"]);
            callers = callers.concat([["e", c, "(cenv)"].join("")]);
        }

        var args_evald = evalers.join("");
        var return_val = ["return function(cenv) { return ", name, "(", callers.join(", "), "); };"].join("");
        return new Function(["args, env, eval0"], [args_evald, return_val].join("\n"));
    }

    function veval(exp, env) {
        return eval0(exp, env)([]);
    }
    
    function build_env(len, e, cenv) {
        var new_env = new Array(len);
        var i = 0;
        while(e !== null) {
            new_env[i++] = e.car(cenv);
            e = e.cdr;
        } return new_env;
    }

    function fresh_n(n, c) {
        var m = new Array(n);
        while(n-- > 0) {
            m[n] = mkvar(c++);
        } return [m, c];
    }

    function map_stream(fn, stream) {
        return function() {
            var $ = pull(stream);
            return ($ == null) ? null : cons(fn($.car), map_stream(fn, $.cdr));
        };
    }

    function query_stream(q, qenv, mks) {
        var $ = q(mks);
        var run_queries = function(mks) {
            var qm = map(function(p) { return cons(p.car.string, p.cdr()()); }, qenv);
            return query_map(qm, mks);
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

    function run_expression(p) {
        var desugared = desugar(p, null);
        var lifted = lift_frees(desugared);

        var exp = lifted.car;
        var env = lifted.cdr.car;
        var mks = lifted.cdr.cdr.car;
        var evald = veval(exp, env);

        if(procedurep(evald)) {
            var q$ = query_stream(evald, env, mks);
            return stream_generator(q$);
        } else if (env === null) {
            return evald;
        } else {
            throw "unbound variables: " + pretty_print(map(car, env));
        }
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

    this.reset = function() { toplevel = new Object(null); };
    this.eval = function(ast) { return run_program(ast); };
    this.read_eval = function(text) { return run_program(read_program(text)); };
}
