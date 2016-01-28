var runtime = require('./base');
var Immutable = require('immutable');
var pairp = runtime.pairp;
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

function Var(c) { this.c = c; }
function mkvar(c) { return new Var(c); }
function varp(x) { return (x instanceof Var); }
function vareq(x1, x2) { return x1.c === x2.c; }

function MiniKanrenState(s, c, d, ty, ab) {
    this.substitution = s;
    this.counter = c;
    this.diseq = d;
    this.types = ty;
    this.absentee = ab;
}
function Mks(s, c, d, ty, ab) { return new MiniKanrenState(s, c, d, ty, ab); }

var not_found = [];
function walk(u, s) {
    var pr;
    // console.log('WALK', arguments);
    // console.log('WALK store', s);
    while(varp(u)) {
        pr = s.get(u.c, not_found);
        if (pr === not_found) {
            return u;
        } else {
            u = pr;
        }
    } return u;
}

function occurs_check(x, v, s) {
    var v1 = walk(v, s);
    if(varp(v1)) {
        return vareq(v1, x);
    } else if (pairp(v1)) {
        return occurs_check(x, v1.car, s) || occurs_check(x, v1.cdr, s);
    } else {
        return false;
    }
}

function ext_s_check(x, v, s) {
    return occurs_check(x, v, s) ? false : s.set(x.c, v);
}

function eqeq(u, v) {
    return function _do_eqeq (mks) {
        // console.log('eqeq', u, v, mks);
        var s = unify(u, v, mks.substitution);
        return s !== false ? normalize_constraint_store(Mks(s, mks.counter, mks.diseq, mks.types, mks.absentee)) : mzero;
    };
}

function noteqeq(u, v) {
    return function _do_noteqeq (mks) {
        var d = disequality(u, v, mks.substitution);
        return d !== false ? unit(Mks(mks.substitution, mks.counter, cons(d, mks.diseq), mks.types, mks.absentee)) : mzero;
    };
}

function type_check(v, p, s, ty) {
    var v1 = walk(v, s);
    if (varp(v1)) {
        var existing_type = ty.get(v1, false);
        if(existing_type && existing_type !== p) {
            return false;
        } else { // add constraint
            return ty.set(v1, p);
        }
    } else { // ground; run test
        return p(v1) ? ty : false;
    }
}

function symbolo(s) { return typeo(s, symbolp); }
function numbero(n) { return typeo(n, numberp); }

function typeo(v, p) {
    return function _do_typeo (mks) {
        var s = mks.substitution;
        var ty = mks.types;
        var ty1 = type_check(v, p, s, ty);
        if (!ty1) {
            return mzero;
        } else if (ty1 === ty) {
            return unit(mks);
        } else {
            var mks1 = Mks(mks.substitution, mks.counter, mks.diseq, ty1, mks.absentee);
            return normalize_constraint_store(mks1);
        }
    };
}

function absento(s, f) {
    return function _do_absento (mks) {
        return normalize_constraint_store(Mks(mks.substitution, mks.counter, mks.diseq, mks.types, cons(cons(s, f), mks.absentee)));
    };
}

function unit(mks) { return cons(mks, mzero); }
var mzero = null;

function unify(u, v, s) {
    // console.log('unify', u, v, s);
    var u1 = walk(u, s);
    var v1 = walk(v, s);
    if (varp(u1) && varp(v1) && vareq(u1, v1)) { return s; }
    else if (varp(u1)) { return ext_s_check(u1, v1, s); }
    else if (varp(v1)) { return ext_s_check(v1, u1, s); }
    else if (pairp(u1) && pairp(v1)) {
        var s1 = unify(u1.car, v1.car, s);
        return (s1 !== false) && unify(u1.cdr, v1.cdr, s1);
    } else {
        return (u1 === v1) && s;
    }
}

function ext_s_check_prefix(x, v, s, cs) {
    if (occurs_check(x, v, s)) {
        return false;
    } else {
        return cons(s.set(x.c, v), cons(cons(x, v), cs));
    }
}

function unify_prefix(u, v, s, cs) {
    var u1 = walk(u, s);
    var v1 = walk(v, s);
    if (varp(u1) && varp(v1) && vareq(u1, v1)) { return cons(s, cs); }
    else if (varp(u1)) { return ext_s_check_prefix(u1, v1, s, cs); }
    else if (varp(v1)) { return ext_s_check_prefix(v1, u1, s, cs); }
    else if (pairp(u1) && pairp(v1)) {
        var s_cs = unify_prefix(u1.car, v1.car, s, cs);
        return (s_cs !== false) && unify_prefix(u1.cdr, v1.cdr, s_cs.car, s_cs.cdr);
    } else {
        return (u1 === v1) && cons(s, cs);
    }
}

function disequality(u, v, s) {
    var s_cs_hat = unify_prefix(u, v, s, null);
    if(s_cs_hat !== false) {
        var d = s_cs_hat.cdr;
        return (d === null) ? false : d;
    }
    else {
        return null;
    }
}

function normalize_constraint_store(mks) {
    var s = mks.substitution;
    var c = mks.counter;
    var d = mks.diseq;
    var dn = null;
    var ty = mks.types;
    var tyn = Immutable.Map();
    var abs = mks.absentee;
    var absn = null;
    // console.log("NORMALIZE", mks);
    // console.log("IMMUTABLE", tyn, Immutable, Immutable.Map, Immutable.Map( ));


    // Normalize the type constraints
    ty.forEach(function _iter_ty (p, v) {
        tyn = type_check(v, p, s, tyn);
        return tyn;
    });
    if (!tyn) { return mzero; }

    // normalize the disequality constraints
    while(d !== null) {
        var es = d.car;

        if(es !== null) {
            var d_hat = disequality(map(car, es), map(cdr, es), s);

            if(d_hat === false) {
                return mzero;
            }

            dn = cons(d_hat, dn);
        }

        d = d.cdr;
    }

    // normalize the absento constraints
    while(abs !== null) {
        var abs_cur = abs.car;
        abs = abs.cdr;

        var abs_s = walk(abs_cur.car, s);
        var abs_f = walk(abs_cur.cdr, s);

        // defer until both terms are ground
        if (varp(abs_f) || varp(abs_s)) {
            absn = cons(cons(abs_s, abs_f), absn);
        }
        // split and requeue
        else if (pairp(abs_f)) {
            abs = cons(cons(abs_s, abs_f.car),
                       cons(cons(abs_s, abs_f.cdr), abs ));
        }
        // both are ground and atomic; check for eqv?
        else if (abs_s === abs_f) {
            return mzero;
        }
        // forget constraint, it can never fail
    }

    return unit(Mks(s, c, dn, tyn, absn));
}

function call_fresh(f) {
    return function _call_fresh (mks) {
        var c = mks.counter;
        return f(mkvar(c))(Mks(mks.substitution, (c + 1), mks.diseq, mks.types, mks.absentee));
    };
}

function disj(g1, g2) {
    return function _disj (mks) { return mplus(g1(mks), g2(mks)); };
}
function conj(g1, g2) {
    return function _conj (mks) { return bind(g1(mks), g2); };
}
 
function mplus($1, $2) {
    if ($1 === null) {
        return $2;
    } else if (procedurep($1)) {
        return function() { return mplus($2, $1()); };
    } else {
        return cons($1.car, mplus($1.cdr, $2));
    }
}

function bind($, g) {
    if ($ === null) {
        return mzero;
    } else if (procedurep($)) {
        return function _bind_proc () { return bind($(), g); };
    } else {
        return mplus(g($.car), bind($.cdr, g));
    }
}

function pull($) {
    while(procedurep($)) {
        $ = $();
    } return $;
}

function take(n, $) {
    if (n <= 0) {
        return null;
    } else {
        var $1 = pull($);
        return ($1 === null) ? null : cons($1.car, take(n - 1, $1.cdr));
    }
}

function take_all($) {
    $ = pull($);
    return ($ === null) ? null : cons($.car, take_all($.cdr));
}

function reify(v, s) {
    var v1 = walk_star(v, s);
    return walk_star(v1, reify_s(v1, Immutable.Map()));
}

function walk_star(v, s) {
    var v1 = walk(v, s);
    if (varp(v1)) {
        return v1;
    } else if (pairp(v1)) {
        return cons(walk_star(v1.car, s),
                    walk_star(v1.cdr, s));
    } else {
        return v1;
    }
}

function reify_s(v, s) {
    var v1 = walk(v, s);
    if (varp(v1)) {
        return s.set(v1.c, reify_name(s.size));
    } else if (pairp(v1)) {
        return reify_s(v1.cdr, reify_s(v1.car, s));
    } else {
        return s;
    }
}

function reify_name(n) {
    return { toString: function _reify_name_to_s () { return ["_", n].join("."); } };
}

function pred_to_tag(p) {
    return assq(p, list(cons(symbolp, intern("sym")),
                        cons(numberp, intern("num")))).cdr;
}

function query_map(qm, mks) {
    var s = mks.substitution;
    var d = mks.diseq;
    var t = mks.types;
    // convert the type store to alist
    var t1 = t.reduce(function _reduce_query_map (m, v, k) { return cons(cons(k, v), m); }, null);

    var sq1 = walk_star(qm, s);
    var dq1 = walk_star(d, s);
    var tq1 = walk_star(t1, s);
    var q = walk_star(list(sq1, dq1, tq1), reify_s(list(sq1, dq1, tq1), Immutable.Map()));

    return print_constraints(q.car, q.cdr.car, q.cdr.cdr.car, s);
}

function print_constraints(sq, dq, tq, s) {
    var subs = foldl(sq, [], function _print_constraints (m, a_v) {
        return m.concat([a_v.car, ": ", pretty_print(a_v.cdr), "\n"]);
    });

    var present_d = function _present_d (dd) {
        // dd is a disjunction of disequalities
        var diseqs = map(function _iter_map (a){ return list(intern("=/="), a.car, a.cdr); }, dd);
        if (length(diseqs) > 1) {
            return pretty_print(cons(intern("or"), diseqs));
        } else if (diseqs !== null) {
            return pretty_print(diseqs.car);
        } else {
            return null;
        }
    };
    var present_t = function _present_t (tt) {
        return pretty_print(list(pred_to_tag(tt.cdr), tt.car));
    }
    return (dq !== null || tq !== null) ?
        (subs
         .concat(["{"])
         .concat(intersperse_map(dq, present_d, ", "))
         .concat([", "])
         .concat(intersperse_map(tq, present_t, ", "))
         .concat(["}\n"]).join("")) :
        subs.join("");
}

function intersperse_map(l, f, sep) {
    var m = [];
    var r;
    while(l !== null) {
        r = f(l.car);
        m = r === null ? m : m.concat([r, (l.cdr === null ? "" : sep)]);
        l = l.cdr;
    }
    return m;
}

function build_num(n) {
    if((n % 2) === 1) {
        return cons(1, build_num(Math.floor((n - 1) / 2)));
    } else if (n !== 0 && (n % 2) === 0) {
        return cons(0, build_num(Math.floor(n / 2)));
    } else {
        return null;
    }
}

exports = module.exports = Mks;

exports.Var = Var;
exports.mkvar = mkvar;
exports.varp = varp;
exports.vareq = vareq;
exports.MiniKanrenState = MiniKanrenState;
exports.walk = walk;
exports.occurs_check = occurs_check;
exports.ext_s_check = ext_s_check;
exports.eqeq = eqeq;
exports.noteqeq = noteqeq;
exports.type_check = type_check;
exports.symbolo = symbolo;
exports.numbero = numbero;
exports.typeo = typeo;
exports.absento = absento;
exports.unit = unit;
exports.unify = unify;
exports.ext_s_check_prefix = ext_s_check_prefix;
exports.unify_prefix = unify_prefix;
exports.disequality = disequality;
exports.normalize_constraint_store = normalize_constraint_store;
exports.call_fresh = call_fresh;
exports.disj = disj;
exports.conj = conj;
exports.mplus = mplus;
exports.bind = bind;
exports.pull = pull;
exports.take = take;
exports.take_all = take_all;
exports.reify = reify;
exports.walk_star = walk_star;
exports.reify_s = reify_s;
exports.reify_name = reify_name;
exports.pred_to_tag = pred_to_tag;
exports.query_map = query_map;
exports.print_constraints = print_constraints;
exports.intersperse_map = intersperse_map;
exports.build_num = build_num;

