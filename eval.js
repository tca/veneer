function VeneerVM() {
    var toplevel = new Object(null);

    function register_define(exp) {
        if (pairp(exp) && exp.car === intern("define")) {
            var a = pairp(exp.cdr.car) ? exp.cdr.car.car : exp.cdr.car;
            toplevel[a.string] = ref(null);
        }
    }

    function quote_desugar(exp) {
        if (pairp(exp)) {
            return meta(list(meta(intern("cons"), {tag:"var"}), quote_desugar(exp.car), quote_desugar(exp.cdr)), {tag:"app-builtin"});
        } else if (exp == null) {
            return meta(list(intern("quote"), null), { tag: "quoted" });
        }else if(constantp(exp)) {
            return meta(exp, {tag:"const"});
        } else {
            return meta(list(intern("quote"), exp), { tag: "quoted" });
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

    function Meta(val, meta) {
        this.val = val;
        this.meta = meta || {};
    }
    function meta(v, meta) { return new Meta(v, meta); }

    function desugar(exp, env) {
        if(exp instanceof Meta) { return exp; }
        if(pairp(exp)) {
            // application
            var app = false;
            if(symbolp(exp.car) && (lookup(exp.car, env) || toplevel.hasOwnProperty(exp.car.string))
               || pairp(exp.car)) {
                return meta(map(function(e) { return desugar(e, env); }, exp),
                            { tag: "app" });
            }
            // special forms & builtins
            switch(exp.car) {
            case intern("define"):
                var name;
                var body;
                if(pairp(exp.cdr.car)) {
                    // (define (x y z) f) => (define x (lambda (y z) f))
                    name = exp.cdr.car.car;
                    body = cons(intern("lambda"), cons(exp.cdr.car.cdr, exp.cdr.cdr));
                } else {
                    name = exp.cdr.car;
                    body = exp.cdr.cdr.car;
                }
                return meta(list(exp.car, name,  desugar(body, env)), { tag: "define" });
            case intern("quote"):
                var val = quote_desugar(exp.cdr.car);
                // val.meta.constp = true;
                return val;
            case intern("quasiquote"):
                return desugar(quasiquote_desugar(exp.cdr.car, 1, env), env);
            case intern("zzz"):
                return meta(list(exp.car, desugar(exp.cdr.car, env)),
                            { tag: "zzz" });
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
                return meta(cons(exp.car, map(function(f) { return desugar(f, env); }, exp.cdr)),
                            { tag: "begin" });
            case intern("fresh"):
                var bindings = exp.cdr.car;
                var body = exp.cdr.cdr;
                if (bindings === null) {
                    return desugar(cons(intern("conj"), body), env);
                } else {
                    var fn = list(intern("lambda"), bindings, cons(intern("conj"), body));
                    var body1 = desugar(fn, env);
                    var len = desugar(length(bindings), env);
                    return meta(list(intern("apply/fresh-n"), len, body1),
                                { tag: "fresh" });
                }
            case intern("lambda"):
                var bindings = exp.cdr.car;
                var body = exp.cdr.cdr;
                var env1 = foldl(bindings, env, augment_env);
                var body1 = desugar(cons(intern("begin"), body), env1);
                return meta(list(exp.car, exp.cdr.car, body1),
                            { tag: "lambda" });
            default:
                if(builtins.hasOwnProperty(exp.car.string)) {
                    return meta(cons(meta(exp.car, { tag: "var" }), map(function(f) { return desugar(f, env); }, exp.cdr)),
                               { tag: "app-builtin" });
                } else if (exp.car === intern("list")) {
                    return meta(cons(meta(exp.car, { tag: "var" }), map(function(f) { return desugar(f, env); }, exp.cdr)),
                                { tag: "app-builtin" });
                } else {
                    throw new Error("unkown exp: " + pretty_print(exp));
                }
            }
        } else if(constantp(exp)) {
            return meta(exp, { tag: "const" });
        } else if(symbolp(exp)) {
            return meta(exp, { tag: "var" });
        } else {
            throw new Error("unkown exp: " + pretty_print(exp));
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
        var existing = lookup(a, envu);
        if (existing) {
            return existing;
        } else {
            env.set(cons(cons(a, v), envu));
            return v;
        }
    }

    function frees(exp, env, lenv, fenv) {
        switch(exp.meta.tag) {
        case "const": case "quoted":
            return exp;
        case "define":
            var name = exp.val.cdr.car;
            var dfenv = ref(null);
            // add self to env once mutable vars works, unless toplevel
            var ret = list(exp.val.car, name, frees(exp.val.cdr.cdr.car, env, lenv, dfenv));
            if(dfenv.get() === null) {
                return meta(ret, exp.meta);
            } else {
                throw ("free variables in define: " + name.string + pretty_print(map(car, dfenv.get())));
            }
        case "lambda":
            var bindings = exp.val.cdr.car;
            var body = exp.val.cdr.cdr;
            var e1 = foldl(bindings, env, function(e, a) { return cons(cons(a, a), e); });
            var inner_frees = ref(null);
            var proper_frees = null;

            var re = cons(exp.val.car, cons(bindings, map(function(x) {
                return frees(x, e1, bindings, inner_frees);
            }, body)));

            map(function(v) {
                if (!memq(v.car, bindings)) {
                    extend_boxed(fenv, v.car, v.cdr);
                    proper_frees = cons(v.cdr, proper_frees);
                }
            }, inner_frees.get());

            exp.meta.frees = proper_frees;
            return meta(re, exp.meta);
        case "begin": case "zzz": case "fresh":
            return meta(cons(exp.val.car, map(function(x) { return frees(x, env, lenv, fenv); }, exp.val.cdr)),
                        exp.meta);
        case "app": case "app-builtin":
            return meta(map(function(x) { return frees(x, env, lenv, fenv); }, exp.val), exp.meta);
        case "var":
            if (memq(exp.val, lenv)) { return exp; }
            if (lookup(exp.val, env)) { return meta(extend_boxed(fenv, exp.val, exp.val), exp.meta); }
            if (toplevel.hasOwnProperty(exp.val.string)) { return exp; }
            if (exp.val === intern("list")) { return exp; } // TODO: remove once varargs added
            if (builtins.hasOwnProperty(exp.val.string)) { return exp; }
            return meta(extend_boxed(fenv, exp.val, exp.val), exp.meta);
        default:
            throw new Error("unkown exp: " + pretty_print(exp.val));
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
        // if(exp.meta.constp) {
        //     exp.meta.constp = false;
        //     var val = eval0(exp, env)();
        //     return function(cenv) { return val; };
        // }
        switch(exp.meta.tag) {
        case "app":
            var clos = eval0(exp.val.car, env);
            var args = foldl(exp.val.cdr, null, function(m, e) {
                return cons(eval0(e, env), m);
            });
            var len = length(args);
            return function(cenv) {
                var clos1 = clos(cenv);
                return clos1.car(build_env(len, args, cenv).concat(clos1.cdr));
            };
        case "define":
            var result = eval0(exp.val.cdr.cdr.car, env);
            toplevel[exp.val.cdr.car.string].set(result());
            return function(cenv) { return true; };
        case "quoted":
            var val = exp.val.cdr.car;
            return function(cenv) { return val };
        case "zzz":
            var e1 = eval0(exp.val.cdr.car, env);
            return function(cenv) { return function(mks) { return function() { return e1(cenv)(mks); }; }; };
        case "begin":
            if (exp.val.cdr == null) { throw new Error("empty begin"); }
            else if (exp.val.cdr.cdr == null) {
                var e1 = eval0(exp.val.cdr.car, env);
                return e1;
            } else {
                return generate_begin_code(length(exp.val.cdr))(exp.val.cdr, env, eval0);
            }
        case "lambda":
            var bindings = exp.val.cdr.car;
            var body = exp.val.cdr.cdr.car;
            var free_env = foldl(reverse(exp.meta.frees), null, augment_env);
            var env1 = foldl(bindings, free_env, augment_env);
            var len = length(exp.meta.frees);
            var free_env1 = map(function(v) { return eval0(meta(v, { tag: "var" }), env); }, exp.meta.frees);
            var closure_body = eval0(body, env1);
            var closure_env_build = function(cenv) { return build_env(len, free_env1, cenv); };
            var closure = function(cenv) { return cons(closure_body, closure_env_build(cenv)); };
            return closure;
        case "fresh":
            var len = exp.val.cdr.car.val;
            var fn = exp.val.cdr.cdr.car;
            var closure = eval0(fn, env);
            return function(cenv) { return apply_fresh(len, closure, cenv); };
        case "app-builtin":
            if (exp.val.car.val === intern("list")) {
                var args = map(function(e) { return eval0(e, env); }, exp.val.cdr);
                return function(cenv) {
                    return map(function(a) { return a(cenv); }, args);
                };
            }
            return builtins[exp.val.car.val.string](exp.val.cdr, env, eval0);
        case "const":
            var val = exp.val
            return function(cenv) { return val; };
        case "var":
            var v = lookup_calc(exp.val, env);
            if (v) {
                return v;
            } else if(toplevel.hasOwnProperty(exp.val.string)) {
                var box = toplevel[exp.val.string];
                return function(cenv) { return box.get(); };
            } else {
                throw new Error("unbound variable: " + pretty_print(exp.val));
            }
        default:
            throw new Error("unkown exp: " + pretty_print(exp.val));
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

    function generate_begin_code(arity) {
        var c = 0;
        var evalers = [];
        var callers = [];

        for(c = 0; c < arity; c++) {
            evalers = evalers.concat(["var e", c, " = eval0(nth(args, ", c+1, "), env);\n"]);
            var prefix = c < arity ? "" : "return ";
            callers = callers.concat([[prefix, "e", c, "(cenv)"].join("")]);
        }

        var args_evald = evalers.join("");
        var return_val = ["return function(cenv) { ", callers.join("; "), " };"].join("");
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

    function apply_fresh(len, closure, cenv) {
        var closure1 = closure(cenv);
        var closure_env = closure1.cdr;
        var closure_fn = closure1.car;
        return function(mks) {
            var c = mks.counter;
            var e1_c1 = fresh_n(len, c);
            var mks1 = Mks(mks.substitution, e1_c1[1], mks.diseq, mks.types, mks.absentee);
            return closure_fn(e1_c1[0].concat(closure_env))(mks1);
        };
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
