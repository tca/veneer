function VeneerVM() {
    var toplevel = new Object(null);

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

    function quasiquote_desugar(exp, n) {
        if (pairp(exp)) {
            if (exp.car === intern("unquote")) {
                if (n === 1) {
                    return desugar(exp.cdr.car);
                } else {
                    return list(intern("list"), list(intern("quote"), intern("unquote")),
                                quasiquote_desugar(exp.cdr.car, n - 1));
                }
            } else if (exp.car === intern("quasiquote")) {
                return  list(intern("list"), list(intern("quote"), intern("quasiquote")),
                             quasiquote_desugar(exp.cdr.car, n + 1));
            } else {
                return list(intern("cons"), quasiquote_desugar(exp.car, n),
                            quasiquote_desugar(exp.cdr, n));
            }
        } else {
            return quote_desugar(exp);
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
            case intern("quasiquote"): return quasiquote_desugar(exp.cdr.car, 1);
            default: return cons(desugar(exp.car), desugar(exp.cdr));
            }
        } else {
            return exp;
        }
    }

    function register_define(exp) {
        if (pairp(exp) && exp.car === intern("define")) {
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
                // special forms & macros
            case intern("define"):
                var a = exp.cdr.car;
                toplevel[a.string] = null;
                return list(exp.car, exp.cdr.car, frees(exp.cdr.cdr.car, cons(cons(a, a), null), null));
            case intern("quote"): return exp;
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
            case intern("conde"):
            case intern("zzz"):
                return cons(exp.car, map(function(x) { return frees(x, env, fenv); }, exp.cdr));
            default:
                return map(function(x) { return frees(x, env, fenv); }, exp);
            }
        } else if(constantp(exp)) {
            return exp;
        } else if(symbolp(exp)) {
            // bound variables
            if (lookup(exp, env) || toplevel.hasOwnProperty(exp.string)) { return exp; }
            switch(exp) {
                // builtins
            case intern("cons"):
            case intern("list"):
            case intern("=="):
            case intern("=/="):
            case intern("conj"):
            case intern("disj"):
            case intern("symbolo"):
            case intern("numbero"):
            case intern("absento"):
            case intern("build-num"):
                return exp;
                // free variables
            default:
                if(fenv) {
                    var v = lookup(exp, fenv.get());
                    if (v) { return v; }
                    var gen = gensym(exp.string);
                    fenv.set(cons(cons(exp, gen), fenv.get()));
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
        while(xs != null) {
            if (x.string === xs.car.car.string) { return xs.car.cdr(n); }
            else { n++; xs = xs.cdr; }
        } return false;
    }

    function augment_env(env, name) {
        var binding = cons(name, function (offset) { return function(cenv) { return cenv.get(offset, not_found); }; });
        return cons(binding, env);
    }

    function lift_frees(exp) {
        var free_env = ref(null);
        var exp1 = frees(exp, null, free_env);
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
                var args = reverse(map(function(e) { return eval0(e, env); }, exp.cdr));
                return function(cenv) {
                    var cenv1 = foldl(args, cenv, function(m, c) {
                        return m.unshift(c(cenv));
                    });
                    return clos(cenv1);
                };
            }
            // special forms & builtins
            switch(exp.car) {
            case intern("define"):
                var result = eval0(exp.cdr.cdr.car, env);
                toplevel[exp.cdr.car.string] = result;
                return function(cenv) { return unit; };
            case intern("quote"):
                return function(cenv) { return exp.cdr.car; };
            case intern("zzz"):
                var e1 = eval0(exp.cdr.car, env);
                return function(cenv) { return function(mks) { return function() { return e1(cenv)(mks); }; }; };
            case intern("conde"):
                var clauses = map(function(row) { return cons(intern("conj"), row); }, exp.cdr);
                return eval0(cons(intern("disj"), clauses), env);
            case intern("conj"):
                if (exp.cdr == null) { throw "error: empty conj"; }
                else if (exp.cdr.cdr == null) {
                    var e1 = eval0(list(intern("zzz"), exp.cdr.car), env);
                    return e1;
                } else {
                    var e1 = list(intern("zzz"), exp.cdr.car);
                    var e2 = cons(intern("conj"), exp.cdr.cdr);
                    return eval0(list(intern("conj%"), e1, e2), env);
                }
            case intern("disj"):
                if (exp.cdr == null) { throw "error: empty disj"; }
                else if (exp.cdr.cdr == null) {
                    var e1 = eval0(list(intern("zzz"), exp.cdr.car), env);
                    return e1;
                } else {
                    var e1 = list(intern("zzz"), exp.cdr.car);
                    var e2 = cons(intern("disj"), exp.cdr.cdr);
                    return eval0(list(intern("disj%"), e1, e2), env);
                }
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
            case intern("fresh"):
                var bindings = exp.cdr.car;
                var body = exp.cdr.cdr;
                var body1 = eval0(list(intern("lambda"), bindings,
                                       cons(intern("conj"), body)),
                                  env);
                var len = length(bindings);

                return function(cenv) {
                    return function(mks) {
                        var c = mks.counter;
                        var e1_c1 = fresh_n(len, c, cenv);
                        var mks1 = Mks(mks.substitution, e1_c1[1], mks.diseq, mks.types, mks.absentee)
                        return body1(e1_c1[0])(mks1);
                    };
                };
            case intern("lambda"):
                var bindings = reverse(exp.cdr.car);
                var body = exp.cdr.cdr;

                var env1 = foldl(bindings, env, augment_env);
                var body1 = eval0(cons(intern("begin"), body), env1);

                return body1;
            case intern("conj%"):
                var e1 = eval0(exp.cdr.car, env);
                var e2 = eval0(exp.cdr.cdr, env);
                return function(cenv) { return conj(e1(cenv), e2(cenv)); };
            case intern("disj%"):
                var e1 = eval0(exp.cdr.car, env);
                var e2 = eval0(exp.cdr.cdr, env);
                return function(cenv) { return disj(e1(cenv), e2(cenv)); };
            // these are builtin functions that we want to call directly instead of building a cenv
            case intern("cons"):
                var e1 = eval0(exp.cdr.car, env);
                var e2 = eval0(exp.cdr.cdr.car, env);
                return function(cenv) { return cons(e1(cenv), e2(cenv)); };
            case intern("list"):
                var args = map(function(e) { return eval0(e, env); }, exp.cdr);
                return function(cenv) {
                    return map(function(a) { return a(cenv); }, args);
                };
            case intern("=="):
                var e1 = eval0(exp.cdr.car, env);
                var e2 = eval0(exp.cdr.cdr.car, env);
                return function(cenv) { return eqeq(e1(cenv), e2(cenv)); };
            case intern("=/="):
                var e1 = eval0(exp.cdr.car, env);
                var e2 = eval0(exp.cdr.cdr.car, env);
                return function(cenv) { return noteqeq(e1(cenv), e2(cenv)); };
            case intern("symbolo"):
                var e1 = eval0(exp.cdr.car, env);
                return function(cenv) { return symbolo(e1(cenv)); };
            case intern("numbero"):
                var e1 = eval0(exp.cdr.car, env);
                return function(cenv) { return numbero(e1(cenv)); };
            case intern("absento"):
                var e1 = eval0(exp.cdr.car, env);
                var e2 = eval0(exp.cdr.cdr.car, env);
                return function(cenv) { return absento(e1(cenv), e2(cenv)); };
            case intern("build-num"):
                var e1 = eval0(exp.cdr.car, env);
                return function(cenv) { return build_num(e1(cenv)); };

            default:
                throw "unkown exp: " + pretty_print(exp);
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
                throw "unbound variable: " + exp.string;
            }
        } else {
            throw "unkown exp: " + pretty_print(exp);
        }
    }

    function veval(exp, env) {
        return eval0(exp, env)(Immutable.Stack());
    }

    function fresh_n(n, c, v) {
        while(n-- > 0) {
            v = v.unshift(mkvar(c));
            c = c + 1;
        } return [v, c];
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
        var desugared = desugar(p);
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
