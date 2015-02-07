
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
                return list(exp.car, exp.cdr.car.car, cons(intern("rel"), cons(exp.cdr.car.cdr, desugar(exp.cdr.cdr))));
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

function lookup(x, xs) {
    while(xs != null) {
        if (x.string === xs.car.car.string) { return xs.car.cdr; }
        else { xs = xs.cdr; }
    } return false;
}

function frees(exp, env, fenv) {
    if(pairp(exp)) {
        switch(exp.car) {
        case intern("define"):
            var a = exp.cdr.car;
            toplevel[a.string] = null;
            // TODO: free variables in definitions?
            return list(exp.car, exp.cdr.car, frees(exp.cdr.cdr.car, cons(cons(a, a), null), null));
        case intern("quote"): return exp;
        case intern("cons"):
            return cons(exp.car, map(function(x) { return frees(x, env, fenv); }, exp.cdr));
        case intern("=="):
            return cons(exp.car, map(function(x) { return frees(x, env, fenv); }, exp.cdr));
        case intern("conj"):
            return cons(exp.car, map(function(x) { return frees(x, env, fenv); }, exp.cdr));
        case intern("disj"):
            return cons(exp.car, map(function(x) { return frees(x, env, fenv); }, exp.cdr));
        case intern("rel"):
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

// returns list(exp, env, s_c)
function lift_frees(exp) {
    var free_env = ref(null);
    var exp1 = frees(exp, null, free_env);
    var e1_c1 = foldl(free_env.get(), cons(null, 0),
                      function(e_c, a) {
                          var var1 = mkvar(e_c.cdr);
                          return cons(cons(cons(a.cdr, function(_) { return var1; }), e_c.car), e_c.cdr+1); });
    return list(exp1, e1_c1.car, cons(null ,e1_c1.cdr));
}

function eval0(exp, env) {
    if(pairp(exp)) {
        switch(exp.car) {
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
        case intern("conj"):
            if (exp.cdr == null) { throw "error: empty conj"; }
            else if (exp.cdr.cdr == null) {
                var e1 = eval0(exp.cdr.car, env);
                return function(cenv) { return function(s_c) { return function() { return e1(cenv)(s_c); }; }; };
            } else {
                var e1 = eval0(exp.cdr.car, env);
                var e2 = eval0(cons(intern("conj"), exp.cdr.cdr), env);
                return function(cenv) { return conj(function(s_c) { return function() { return e1(cenv)(s_c); }; },
                                                    e2(cenv)); };
            }
        case intern("disj"):
            if (exp.cdr == null) { throw "error: empty conj"; }
            else if (exp.cdr.cdr == null) {
                var e1 = eval0(exp.cdr.car, env);
                return function(cenv) {  return function(s_c) { return function() { return e1(cenv)(s_c); }; }; };
            } else {
                var e1 = eval0(exp.cdr.car, env);
                var e2 = eval0(cons(intern("disj"), exp.cdr.cdr), env);
                return function(cenv) { return disj(function(s_c) { return function() { return e1(cenv)(s_c); }; },
                                                    e2(cenv)); };
            }
        case intern("fresh"):
            var bindings = exp.cdr.car;
            var body = exp.cdr.cdr;
            var body1 = eval0(cons(intern("rel"), exp.cdr), env);

            return function(cenv) {
                return function(s_c) {
                    // make fresh variables as argument list
                    var as_c1 = foldl(bindings, cons(null, s_c.cdr), function(as_c, a) {
                        return cons(cons(mkvar(as_c.cdr), as_c.car), as_c.cdr+1);
                    });
                    
                    return body1(cenv)(as_c1.car)(cons(s_c.car, as_c1.cdr));
                };
            };
        case intern("rel"):
            var bindings = exp.cdr.car;
            var body = exp.cdr.cdr;
            // we get the env by adding (var . offset) pairs to it
            var env1 = foldl(bindings, env,
                             function(e_c, a) {
                                 var offset = e_c.cdr;
                                 var var1 = function(cenv) { return cenv[offset]; }
                                 return cons(cons(cons(a, var1), e_c.car), offset+1); });
            // now we have an (env . cenv_size)
            // var env1 = e1_c1.car;
            var cenv_size = env1.cdr;
            var body1 = eval0(cons(intern("conj"), body), env1);
            // adds fresh variables
            return function(cenv) {
                return function(args) {
                    var fl = cenv.length;
                    // fl .. cenv_size-1 is the fresh variables
                    var m = new Array(cenv_size);
                    var i;
                    // copy parent env...
                    // todo: link environments instead of copy
                    for(i=0; i < fl; i++) {
                        m[i] = cenv[i];
                    }
                    // add arguments calll them with cenv??
                    map(function(a) { m[i++] = a; }, args);
                    return body1(m);
                };
            };
        default: // application
            var evald = map(function(e) { return eval0(e, env); }, exp);
            var fn = evald.car;
            var args = evald.cdr;
            return function(cenv) {
                return fn(cenv)(map(function(a) { return a(cenv); }, args));
            };
        }
    } else if(constantp(exp)) {
        return function(cenv) { return exp; };
    } else if(symbolp(exp)) {
        var v = lookup(exp, env.car);
        if (v) {
            return v;
        } else if(toplevel.hasOwnProperty(exp.string)) {
            var mbox = ref(function() {
                var cache = toplevel[exp.string];
                mbox.set(function() { return cache; })
                return cache;
            });
            return function(cenv) {
                var val = mbox.get()();
                return val(cenv); };
        } else {
            throw ["unbound variable: " + exp.string, env.car];
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
    var s_c = init.cdr.cdr.car;
    var foo = eval0(exp, cons(env, 0))([]);
    var $ = foo(s_c);

    var run_queries = function(s_c) {
        var s = s_c.car;
        var record = new Object(null);
        map(function(x) { record[x.car.string] = query(x.cdr(),s); }, env);
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

var toplevel = new Object(null);
var vm_state = cons(null, mzero);

// TODO: multi-expression programs
function run_program(p) {
    var desugared = desugar(p);
    var lifted = lift_frees(desugared);
    var q$ = query_stream(lifted);
    return stream_generator(q$);
}
