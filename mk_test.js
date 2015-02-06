
function fives(x) {
    return disj(eqeq(x, 5),
                function(a_c) {
                    return function() { return fives(x)(a_c); }
                });
}
function sixes(x) {
    return disj(eqeq(x, 6),
                function(a_c) {
                    return function() { return sixes(x)(a_c); }
                });
}

function node_log(x) { return console.log(require('util').inspect(x, true, 10)); }
var empty_state = cons(null, 0);
var test1 = call_fresh(function (q) { return eqeq(q, 5); })(empty_state);
node_log(test1.car);
node_log("-----");

var fv;
var sv;
var test2 = function(x) {
    fv = x;
    return fives(x);
};

var res = conj(call_fresh(test2), call_fresh(sixes))(empty_state);

node_log(assq(fv, take(5, res).car.car));
