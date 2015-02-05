
function fives(x) {
    return disj(eqeq(x, 5),
                function(a_c) {
                    return function() { return fives(x)(a_c); }
                });
}

var empty_state = cons(null, 0);
var test1 = call_fresh(function (q) { return eqeq(q, 5); })(empty_state);
console.log(test1.car);
var test2 = call_fresh(fives)(empty_state);
console.log(take(5, test2));
