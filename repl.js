
var Immutable = require("./immutable.min.js");
var es = require('event-stream');
var VeneerVM = require('./eval');
var read_program = require('./reader');
var fs = require('fs');
var runtime = require('./base');
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
        cache.push(data)
      } else {
        // sexps.push(result);
        if (result.msg) {
          throw result;
        }
        this.queue(result);
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

function pp (prefix) {
  function iter (data, next) {
    console.log(prefix, runtime.pretty_print(data));
    return next(null, data);
  }
  return es.map(iter);
}

if (!module.parent) {
  var vm = new VeneerVM(read_program, runtime);
  console.log(vm);
  es.pipeline(
    inputs.apply(this, process.argv.slice(2))
  // one line at a time will cause unexpected eof or other errors for valid
  // expressions that continue on the next line.
  , parsing_stream( )
  // , lines( )
  // , get_ast(vm)
  , pp('xxx?')
  // , tap('xxx?')
  );
}
