function Veneer_v1() {
    this.new_editor = function(container, vm, seed) {
        var errors = document.createElement("div");
        errors.className += "errors";
        container.appendChild(errors);

        var options = { mode: "scheme",
                        matchBrackets: true,
                        autoCloseBrackets: true,
                        lineNumbers: true};
        var editor = new CodeMirror(function(ed) {
            container.appendChild(ed);
            return ed;
        }, options);
        
        var repl = document.createElement("div");
        repl.className += "repl";
        container.appendChild(repl);
        
        var dump_button = document.createElement("div");
        dump_button.className += "dump_button";
        dump_button.appendChild(document.createTextNode("run!"));
        container.appendChild(dump_button);

        var clear = document.createElement("hr");
        clear.className += "clear";
        container.appendChild(clear);
        
        var current_input = repl_getline(false);
        function display_error(e) {
            var error = document.createElement("div");
            var error_txt = document.createTextNode(e);
            error.className += "error";
            error.appendChild(error_txt);
            errors.appendChild(error);
            setTimeout(function() { errors.removeChild(error); }, 3000);
        }

        var getTime;
        if (window.performance && window.performance.now && false) {
            getTime = function() { return window.performance.now(); };
        } else {
            getTime = function() { return (new Date()).getTime(); };
        }

        function load_input(inputbox) {
            inputbox = current_input;
            /* var textcontent = inputbox.innerHTML.replace(/<br(\s*)\/*>/ig, '\n') 
               .replace(/<[p|div]\s/ig, '\n$0') 
               .replace(/(<([^>]+)>)/ig, ""); */

            var pass = false;
            var textcontent = inputbox.textContent;
            try {
                var result = vm.read_eval(textcontent);
                var result_elt = document.createElement("div");
                result_elt.className += "result";

                function display_query(generator, parent) {
                    var answer_text = document.createElement("div");
                    var button = document.createElement("button");
                    var append_answer = function(focus) {
                        var answered;
                        var time_before = getTime();
                        var answer_val = generator();
                        var run_time = (getTime() - time_before).toFixed(2);
                        if (answer_val === null) {
                            answered = "No.";
                            answer_val = "";
                            parent.removeChild(button);
                        } else {
                            answered = "Yes.";
                        }
                        var answer_val_pp = answered + " (" + run_time + "ms)\n" + answer_val;
                        var answer_node = document.createTextNode("=> " + answer_val_pp + "\n");
                        answer_text.appendChild(answer_node);

                        if(focus) {
                            button.focus();
                            current_input.scrollIntoView(false);
                        }

                        return false;
                    }
                    button.onclick = function() { return append_answer(true); };
                    button.appendChild(document.createTextNode("More answers!"));
                    parent.appendChild(answer_text);
                    parent.appendChild(button);
                    append_answer(false);
                    return answer_text;
                }

                function display_val(val, parent) {
                    parent.appendChild(document.createTextNode(pretty_print(val)));
                }

                procedurep(result) ? display_query(result, result_elt)
                    : display_val(result, result_elt);

                repl.appendChild(result_elt);
                inputbox.contentEditable = false;
                repl_getline(true);
                return false;
            } catch (e) {
                if(e instanceof ReaderError) {
                    inputbox.appendChild(document.createTextNode("\n"));
                    display_error(e.msg);
                    pass = true;
                    throw e.msg;
                } else {
                    display_error(e);
                    pass = false;
                    throw e;
                }
            } finally { return pass; }
        }

        function repl_getline(focus) {
            var inputbox = document.createElement("pre");
            inputbox.className += "inputbox";
            inputbox.contentEditable = true;
            inputbox.onkeypress = function(e) {
                if (e.keyCode == 13) {
                    return load_input(inputbox);
                }
            };

            repl.appendChild(inputbox);
            if (focus) { inputbox.focus(); }
            current_input = inputbox;
            return inputbox;
        }
        

        var dump_editor = function() {
            vm.reset();
            if (!(typeof seed === 'undefined')) { vm.read_eval(seed); }
            current_input.textContent = editor.getValue();
            load_input(current_input);
            return false;
        }
        dump_button.onclick = dump_editor;

        var shift = false;

        editor.setOption("extraKeys", {
            "Shift-Enter": function(cm) { dump_editor();}
        });

        return { editor: editor, repl: repl, errors: errors, dump_button: dump_button };
    };

 
    this.new_vm = function() { return new VeneerVM(); };
}
