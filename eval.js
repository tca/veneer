var Immutable = require('immutable');
function VeneerVM(reader, runtime, kanren) {
  var read_program = read_program ? read_program : reader;

  var Pair = runtime.Pair;
  var car = runtime.car;
  var cdr = runtime.cdr;
  var pairp = runtime.pairp;
  var cons = runtime.cons;
  var Symbol = runtime.Symbol;
  var gensym = runtime.gensym;
  var intern = runtime.intern;
  var nullp = runtime.nullp;
  var procedurep = runtime.procedurep;
  var symbolp = runtime.symbolp;
  var numberp = runtime.numberp;
  var booleanp = runtime.booleanp;
  var stringp = runtime.stringp;
  var constantp = runtime.constantp;
  var Ref = runtime.Ref;
  var ref = runtime.ref;
  var anyp = runtime.anyp;
  var memq = runtime.memq;
  var assp = runtime.assp;
  var length = runtime.length;
  var nth = runtime.nth;
  var reverse_aux = runtime.reverse_aux;
  var reverse = runtime.reverse;
  var array_slice_list = runtime.array_slice_list;
  var array_to_list = runtime.array_to_list;
  var map = runtime.map;
  var list = runtime.list;
  var foldl = runtime.foldl;
  var foldr = runtime.foldr;
  var assq = runtime.assq;
  var pretty_print = runtime.pretty_print;

  var Mks = kanren;
  var Var = kanren.Var;
  var mkvar = kanren.mkvar;
  var varp = kanren.varp;
  var vareq = kanren.vareq;
  var MiniKanrenState = kanren.MiniKanrenState;
  var walk = kanren.walk;
  var occurs_check = kanren.occurs_check;
  var ext_s_check = kanren.ext_s_check;
  var eqeq = kanren.eqeq;
  var noteqeq = kanren.noteqeq;
  var type_check = kanren.type_check;
  var symbolo = kanren.symbolo;
  var numbero = kanren.numbero;
  var typeo = kanren.typeo;
  var absento = kanren.absento;
  var unit = kanren.unit;
  var unify = kanren.unify;
  var ext_s_check_prefix = kanren.ext_s_check_prefix;
  var unify_prefix = kanren.unify_prefix;
  var disequality = kanren.disequality;
  var normalize_constraint_store = kanren.normalize_constraint_store;
  var call_fresh = kanren.call_fresh;
  var disj = kanren.disj;
  var conj = kanren.conj;
  var mplus = kanren.mplus;
  var bind = kanren.bind;
  var pull = kanren.pull;
  var take = kanren.take;
  var take_all = kanren.take_all;
  var reify = kanren.reify;
  var walk_star = kanren.walk_star;
  var reify_s = kanren.reify_s;
  var reify_name = kanren.reify_name;
  var pred_to_tag = kanren.pred_to_tag;
  var query_map = kanren.query_map;
  var print_constraints = kanren.print_constraints;
  var intersperse_map = kanren.intersperse_map;
  var build_num = kanren.build_num;

    var toplevel = new Object(null);


    function infixen (name, $e0, $e1) {
      switch (name) {
        case '-':
          return $e0 - $e1;
        case '+':
          return $e0 + $e1;
        case '===':
          return $e0 === $e1;
        default:
          console.error('bad infixen');
          break;
      }
    }

    function register_define(exp) {
        if (pairp(exp) && exp.car === intern("define")) {
            var a = pairp(exp.cdr.car) ? exp.cdr.car.car : exp.cdr.car;
            toplevel[a.string] = ref(null);
        }
    }

    function quote_desugar(exp) {
        console.log("ZZZZ", pretty_print(exp) );
        if (pairp(exp)) {
            console.log("YYYY", exp.cdr);
            return meta(list(meta(intern("cons"), {tag:"var"}), quote_desugar(exp.car), quote_desugar(exp.cdr)), {tag:"app-builtin"});
        } else if (exp == null) {
            return meta(list(intern("quote"), null), { tag: "quoted" });
        } else if(constantp(exp)) {
            return meta(exp, {tag:"const"});
        } else {
            return meta(list(intern("quote"), exp), { tag: "quoted" });
        }
    }

    function quasiquote_desugar(exp, n, env) {
        if (pairp(exp)) {
            if (exp.car === intern("unquote")) {
                if (n === 1) {
                    return exp.cdr.car;
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
            return list(intern("quote"), exp);
        }
    }

    function Meta(val, meta) {
        this.val = val;
        this.meta = meta || {};
    }
    function meta(v, meta) { return new Meta(v, meta); }

    function normalize_params(params) {
        var ps = null;
        var rest = null;
        var whole = null;
        while(params !== null) {
            if(symbolp(params)) {
                rest = cons(params, rest);
                whole = cons(params, ps);
                break;
            } else {
                ps = cons(params.car, ps);
                whole = ps;
                params = params.cdr;
            }
        } return { normal: reverse(ps), rest: rest, whole: reverse(whole) };
    }

    function desugar(exp, env) {
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
                val.meta.constp = true;
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
            case intern("if"):
                return meta(cons(exp.car, map(function(f) { return desugar(f, env); }, exp.cdr)),
                            { tag: "if" });
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
                var norm = normalize_params(bindings);
                var env1 = foldl(norm.whole, env, function(e, b) { return cons(cons(b, b), e); });
                var body1 = desugar(cons(intern("begin"), body), env1);
                // console.log("DEBUG LAMBDA", body1, env1, env);
                return meta(list(exp.car, norm.whole, body1),
                            { tag: "lambda", params: norm });
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
        case "begin": case "zzz": case "fresh":
            return meta(cons(exp.val.car, map(function(x) { return frees(x, env, lenv, fenv); }, exp.val.cdr)),
                        exp.meta);
        case "if":
            return meta(cons(exp.val.car, map(function(x) { return frees(x, env, lenv, fenv); }, exp.val.cdr)),
                        exp.meta);
        case "lambda":
            console.log('frees');
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

    function lookup_calc(x, xs) {
        var n = 0;
        while(xs !== null) {
            if (x === xs.car.car) { return xs.car.cdr(n); }
            else { n++; xs = xs.cdr; }
        } return false;
    }

    function augment_cenv(env, name) {
        var binding = cons(name, function (offset) { return function(aenv, cenv) { return cenv[offset]; }; });
        return cons(env.car, cons(binding, env.cdr));
    }

    function augment_aenv(env, name) {
        var binding = cons(name, function (offset) { return function(aenv, cenv) { return aenv[offset]; }; });
        return cons(cons(binding, env.car), env.cdr);
    }

    function augment_aenv_rest(env, name) {
        var binding = cons(name, function (offset) { return function(aenv, cenv) { return array_slice_list(aenv, offset); }; });
        return cons(cons(binding, env.car), env.cdr);
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
        if(exp.meta.constp) {
            exp.meta.constp = false;
            var val = eval0(exp, env)();
            return function(cenv) { return val; };
        }
        switch(exp.meta.tag) {
        case "app":
            var clos = eval0(exp.val.car, env);
            var args = foldl(reverse(exp.val.cdr), null, function(m, e) {
                return cons(eval0(e, env), m);
            });
            var len = length(args);
            return function(aenv, cenv) {
                var clos1 = clos(aenv, cenv);
                return clos1.car(build_env(len, args, aenv, cenv), clos1.cdr);
            };
        case "define":
            var result = eval0(exp.val.cdr.cdr.car, env);
            toplevel[exp.val.cdr.car.string].set(result());
            return function(aenv, cenv) { return true; };
        case "quoted":
            var val = exp.val.cdr.car;
            return function(aenv, cenv) { return val };
        case "begin":
            console.log("WHAT NOW BEGIN");
            if (exp.val.cdr == null) { throw new Error("empty begin"); }
            else if (exp.val.cdr.cdr == null) {
                var e1 = eval0(exp.val.cdr.car, env);
                return e1;
            } else {
                return generate_begin_code(length(exp.val.cdr))(exp.val.cdr, env, eval0);
            }
        case "if":
            var t = eval0(exp.val.cdr.car, env);
            var c = eval0(exp.val.cdr.cdr.car, env);
            var a = eval0(exp.val.cdr.cdr.cdr.car, env);
            return function(aenv, cenv) { return t(aenv, cenv) ? c(aenv, cenv) : a(aenv, cenv); };
        case "lambda":
            var bindings = exp.val.cdr.car;
            var body = exp.val.cdr.cdr.car;
            console.log("DEBUG LAMBDA", body);
            var free_env = foldl(reverse(exp.meta.frees), cons(null, null), augment_cenv);
            var env1_rest = foldl(exp.meta.params.rest, free_env, augment_aenv_rest);
            var env1 = foldl(reverse(exp.meta.params.normal), env1_rest, augment_aenv);
            var len = length(exp.meta.frees);
            var free_env1 = map(function(v) { return eval0(meta(v, { tag: "var" }), env); }, exp.meta.frees);
            var closure_body = eval0(body, env1);
            var closure_env_build = function(aenv, cenv) { return build_env(len, free_env1, aenv, cenv); };
            var closure = function(aenv, cenv) { return cons(closure_body, closure_env_build(aenv, cenv)); };
            return closure;
        case "zzz":
            return (function _zzz ( ) {
              var e1 = eval0(exp.val.cdr.car, env);
              // console.log('HUH 1?', e1, env);
              return function _zzz_1 (aenv, cenv) {
                // console.log('HUH 2?', aenv.map(runtime.pretty_print), cenv.map(runtime.pretty_print));
                return function _zzz_mks_2 (mks) {
                  // console.log('HUH 3?', mks);
                  return function _zzz_3 () {
                    // console.log('HUH 4?', e1);
                    var $v = e1(aenv, cenv);
                    // console.log(e1, '$v?', $v);
                    if (typeof $v == 'undefined') {
                      throw "wowowow";
                    }
                    return $v(mks);
                  };
                };
              };
            })( );
        case "fresh":
            var len = exp.val.cdr.car.val;
            var fn = exp.val.cdr.cdr.car;
            var closure = eval0(fn, env);
            return function(aenv, cenv) { return apply_fresh(len, closure, aenv, cenv); };
        case "app-builtin":
            if (exp.val.car.val === intern("list")) {
                var args = map(function(e) { return eval0(e, env); }, exp.val.cdr);
                return function(aenv, cenv) {
                    return map(function(a) { return a(aenv, cenv); }, args);
                };
            }
            return builtins[exp.val.car.val.string](exp.val.cdr, env, eval0);
        case "const":
            var val = exp.val
            return function(aenv, cenv) { return val; };
        case "var":
            var v;
            v = lookup_calc(exp.val, env.car) || lookup_calc(exp.val, env.cdr);
            if (v) {
                return v;
            } else if(toplevel.hasOwnProperty(exp.val.string)) {
                var box = toplevel[exp.val.string];
                return function(aenv, cenv) { return box.get(); };
            } else {
                throw new Error("unbound variable: " + pretty_print(exp.val));
            }
        default:
            throw new Error("unkown exp: " + pretty_print(exp.val));
        }
    }

    var builtins = new Object(null);
    builtins["cons"] = generate_fn_code("cons", 2);
    builtins["car"] = generate_fn_code("car", 1);
    builtins["cdr"] = generate_fn_code("cdr", 1);
    builtins["null?"] = generate_fn_code("nullp", 1);
    builtins["+"] = generate_fn_code("+", 2, true);
    builtins["-"] = generate_fn_code("-", 2, true);
    builtins["="] = generate_fn_code("===", 2, true);
    builtins["eq?"] = generate_fn_code("===", 2, true);
    builtins["log"] = generate_fn_code("console.log", 1);

    builtins["conj/2"] = generate_fn_code("conj", 2);
    builtins["disj/2"] = generate_fn_code("disj", 2);
    builtins["=="] = generate_fn_code("eqeq", 2);
    builtins["=/="] = generate_fn_code("noteqeq", 2);
    builtins["symbolo"] = generate_fn_code("symbolo", 1);
    builtins["numbero"] = generate_fn_code("numbero", 1);
    builtins["absento"] = generate_fn_code("absento", 2);
    builtins["build-num"] = generate_fn_code("build_num", 1);

    function generate_fn_code(name, arity, infixp) {
        var c = 0;
        var evalers = [];
        var callers = [];


        function do_code (args, env, eval0) {
          var func = kanren[name] || runtime[name];
          if (name == 'console.log') {
            func = function logger ( ) {
              console.log.apply(console, [].slice.apply(arguments).map(function ith (m) {
                return JSON.stringify(m, null, '  ');
              }));
            }
          }
          var $ans = [ ];
          for (c=0; c < arity; c++) {
            (function _iter_eval_arity (v, i) {
              // console.log(arity, 'args', runtime.pretty_print(args));
              // console.log(arity, 'args', args);
              var e0 = eval0(args.car, env);
              args = args.cdr;
              $ans.push(e0);
            })(c);
          }

          function answer (aenv, cenv) {
            var intermediate = [ ];
            $ans.map(function _iter_answers (e0, i) {
              var r = e0(aenv, cenv);
              // console.log('INTERMEDIATE', e0, i, r);
              intermediate.push(r);
            });
            if (infixp) {
                return infixen.apply(this, [name].concat(intermediate));
            } else {
              // console.log('intermediate', intermediate);
              var result = func.apply(this, intermediate);
              // console.log('answer', result);
              if (result && typeof result.cdr === 'undefined') {
                // console.error(name, runtime.pretty_print(result));
                // console.error("ARGS", JSON.stringify(args));
                // throw "bad cdr";
              }
              return result;
            }
          }
          return answer;
        }
        return do_code;

        for(c = 0; c < arity; c++) {
            evalers = evalers.concat(["var e", c, " = eval0(args.car, env);\n"]);
            evalers = evalers.concat(["args = args.cdr;\n"]);
            callers = callers.concat([["e", c, "(aenv, cenv)"].join("")]);
        }
        var args_evald = evalers.join("");

        var return_val;
        if (infixp === true) {
            return_val = ["\n\treturn function(aenv, cenv) {\n\t\treturn ", callers[0], " ", name, " ", callers[1], "; };\n"].join("");
        } else {
            return_val = ["return function(aenv, cenv) { return ", name, "(", callers.join(", "), "); };\n"].join("");
        }
        console.log('NEW FUNCTION', name, arity, 'fn_code');
        console.log([args_evald, return_val].join(""));
        return new Function(["args, env, eval0"], [args_evald, return_val].join("\n"));
    }

    function generate_begin_code(arity) {
        var c = 0;
        var evalers = [];
        var callers = [];

        for(c = 0; c < arity; c++) {
            evalers = evalers.concat(["var e", c, " = eval0(nth(args, ", c+1, "), env);\n"]);
            var prefix = c < arity ? "" : "return ";
            callers = callers.concat([[prefix, "e", c, "(aenv, cenv)"].join("")]);
        }

        var args_evald = evalers.join("");
        var return_val = ["return function(aenv, cenv) { ", callers.join("; "), " };"].join("");
        console.log('NEW FUNCTION', arity, 'begin_code');
        console.log('function', '(', args_evald, ')', "\n" + return_val);
        return new Function(["args, env, eval0"], [args_evald, return_val].join("\n")).bind(this);
    }

    function veval(exp, env) {
        return eval0(exp, env)([], []);
    }
    
    function build_env(len, e, aenv, cenv) {
        var new_env = new Array(len);
        var i = 0;
        while(e !== null) {
            new_env[i++] = e.car(aenv, cenv);
            e = e.cdr;
        } return new_env;
    }

    function fresh_n(n, c) {
        var m = new Array(n);
        while(n-- > 0) {
            m[n] = mkvar(c++);
        } return [m, c];
    }

    function apply_fresh(len, closure, aenv, cenv) {
        var closure1 = closure(aenv, cenv);
        var closure_env = closure1.cdr;
        var closure_fn = closure1.car;
        return function(mks) {
            var c = mks.counter;
            var e1_c1 = fresh_n(len, c);
            var mks1 = Mks(mks.substitution, e1_c1[1], mks.diseq, mks.types, mks.absentee);
            return closure_fn(e1_c1[0], closure_env)(mks1);
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
        var env = cons(null, lifted.cdr.car);
        var mks = lifted.cdr.cdr.car;
        var evald = veval(exp, env);

        if(procedurep(evald)) {
            var q$ = query_stream(evald, env.cdr, mks);
            return stream_generator(q$);
        } else if (env.cdr === null) {
            return evald;
        } else {
            throw "unbound variables: " + pretty_print(map(car, env.cdr));
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
    this.parse_program = function(text) { return read_program(text); };
    this.eval = function(ast) { return run_program(ast); };
    this.read_eval = function(text) { return run_program(read_program(text)); };
}
module.exports = VeneerVM;
