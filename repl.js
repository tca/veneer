
var Immutable = require("./immutable.min.js");
var es = require('event-stream');
var VeneerVM = require('./eval');
var read_program = require('./reader');
var fs = require('fs');
var runtime = require('./base');
var kanren = require('./mk');
// var VeneerVM = require('./veneer');

function inputs (input) {
  var L = [ ];
  var out = es.through(function (d) { this.queue(d); });
  if (!input) {
    L.push(process.stdin);
  } else {
    var args = [].slice.apply(arguments);
    if (args && args.length > 0) {
      L = L.concat(args);
    }
  }

  function iter (elem, next) {
    var from = elem;
    if (!from.pipe) {
      from = fs.createReadStream(elem)
        .on('end', function (ev) {return next( );})
        ;
    }
    from.pipe(out, {end: false });
  }

  function ender (err, remainder) {
    console.log('finished everything', err, remainder);
    out.end( );
  }

  es.pipeline(
    es.readArray(L)
  , es.map(iter)
  , es.writeArray(ender)
  );
  return out;
}

function lines ( ) {
  return es.split( );
}

function get_ast (vm) {
  var line = [ ];
  function iter (data) {
    try {
      var ast = vm.parse_program(data);
      if (ast) {
        this.queue(ast);
      }
    } catch (e) {
      console.error(e);
    }
  }
  return es.through(iter);
}

function tap (prefix) {
  function iter (data, next) {
    console.log(prefix, data);
    return next(null, data);
  }
  return es.map(iter);
}

function parsing_stream ( ) {
  var cache = [ ];
  // var sexps = null;

  function writer (data) {
    if (data) {
      var result = read_program(cache.join("\n") + data);
      if (result && result.msg == 'unexpected eof') {
        cache.push(data);
      } else {
        // sexps.push(result);
        if (result) {
          if (result.msg) {
            throw result;
          }
          this.queue(result);
        }
        cache = [ ];
        // sexps = cons(result, sexps);
      }
    }
  }

  function ender (data) {
    // return reverse_aux(sexps, null);
    this.end( );
  }

  var stream = es.through(writer, ender);
  return stream;
}

function eval_stream (vm) {
  function iter (data, next) {
    try {
      var value = vm.eval(data);
      next(null, value);
    } catch (e) {
      next(e, null);
    }
  }
  return es.map(iter);
}

function run_stream (n) {
  var max = n ? n : 5;
  function iter (data, next) {
    var c = 0;
    function writer (val) {
      if (max > c) {
        var out = runtime.procedurep(val) ? val() : runtime.pretty_print(val);
        if (out) {
          console.log("OUT ELEMENTS", max, c, out);
          this.queue(out);
        }
      } else {
        this.end( );
      }
      c++;
    }
    function ender ( ) {
      next(null, data);
    }
    // var out = runtime.procedurep(val) ? val() : runtime.pretty_print(val);
    var stream = es.through(writer, ender);
    stream.write(data);
  }
  return es.map(iter);
}

function pp (prefix) {
  function iter (data, next) {
    console.log(prefix, runtime.pretty_print(data));
    return next(null, data);
  }
  return es.map(iter);
}

if (!module.parent) {
  var vm = new VeneerVM(read_program, runtime, kanren);
  es.pipeline(
    inputs.apply(this, process.argv.slice(2))
  , parsing_stream( )
  // , pp('xxx?')
  , eval_stream(vm)
  // , run_stream( )
  // , tap('xxx?')
  , es.through(function (val) {
    for (var x=0; x < 5; x++) {
      var out = runtime.procedurep(val) ? val() : runtime.pretty_print(val);
      this.queue(out);
    }
  }).on('error', function (ev) { console.log('EEEK', arguments); })
  // , tap('ANSWERS?\n')
  // , es.stringify( )
  , es.join("\n")
  , process.stdout
  );
}
