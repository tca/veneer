function Veneer_v1() {
    this.new_editor = function(container, vm, seed) {
        container.className += " veneer_container";

        var errors = document.createElement("div");
        errors.className += "errors";
        container.appendChild(errors);

        var cm_options = { mode: "scheme",
                        matchBrackets: true,
                        autoCloseBrackets: true,
                        lineNumbers: false,
                        lineWrapping: true};


        var editor_container = document.createElement("div");
        editor_container.className += "editor_container";
        container.appendChild(editor_container);
        var editor_elt;
        var editor = new CodeMirror(function(ed) {
            editor_container.appendChild(ed);
            editor_elt = ed;
        }, cm_options);
        
        var repl_container = document.createElement("div");
        repl_container.className += "repl_container";
        container.appendChild(repl_container);

        var repl = document.createElement("div");
        repl.className += "repl";
        repl_container.appendChild(repl);
        
        var buttons_container = document.createElement("div");
        buttons_container.className += "buttons_container";
        container.appendChild(buttons_container);

        var dump_button = document.createElement("div");
        dump_button.className += "dump_button";
        dump_button.appendChild(document.createTextNode("run!"));
        dump_button.style.padding = "0 2em";
        buttons_container.appendChild(dump_button);

        var edit_button = document.createElement("div");
        edit_button.className += "edit_button";
        edit_button.appendChild(document.createTextNode("edit"));
        buttons_container.appendChild(edit_button);

        var repl_button = document.createElement("div");
        repl_button.className += "repl_button";
        repl_button.appendChild(document.createTextNode("repl"));
        buttons_container.appendChild(repl_button);

        var edit_mode = "edit";

        var vertical_button = document.createElement("div");
        vertical_button.className += "vertical_button";
        vertical_button.appendChild(document.createTextNode("vertical"));
        buttons_container.appendChild(vertical_button);
        vertical_button.style.float = "right";
        vertical_button.onclick = function() {
            editor_container.style.display="block";
            editor_container.style.width="50%"
            editor_container.style.top="3em";
            editor_container.style.height="auto";
            editor_container.style.bottom="0";

            repl_container.style.display="block";
            repl_container.style.width="50%"
            repl_container.style.top="3em";
            repl_container.style.right="0";
            repl_container.style.height="auto";
            repl_container.style.bottom="0";

            edit_mode = "vertical";
            repl_button.style.display = "none";
            edit_button.style.display = "none";
        }

        var present_button = document.createElement("div");
        present_button.className += "present_button";
        present_button.appendChild(document.createTextNode("present"));
        buttons_container.appendChild(present_button);
        present_button.style.float = "right";
        present_button.onclick = function() {
            editor_container.style.display="block";
            editor_container.style.height="auto";
            editor_container.style.width="100%";
            editor_container.style.bottom="0";

            repl_container.style.display="none";
            repl_container.style.width="100%";
            repl_container.style.height="auto";
            repl_container.style.top="3em";
            repl_container.style.bottom="0";


            edit_mode = "edit";
            repl_button.style.display = "inline";
            edit_button.style.display = "inline";
        }

        // var clear = document.createElement("hr");
        // clear.className += "clear";
        // container.appendChild(clear);
        
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
        if (window.performance && window.performance.now) {
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
            var inputbox = document.createElement("div");
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
        
        var dump_editor = function(event) {
            if (edit_mode === "edit") {
                edit_mode = "repl";
                editor_container.style.display="none";
                repl_container.style.display="block";
            }

            vm.reset();
            if (!(typeof seed === 'undefined')) { vm.read_eval(seed); }
            current_input.textContent = editor.getValue();
            load_input(current_input);

            event.preventDefault();
            return false;
        };
        dump_button.onclick = dump_editor;
        edit_button.onclick = function(event) {
            if (edit_mode === "edit") {
            } else {
                edit_mode = "edit";
                editor_container.style.display="block";
                repl_container.style.display="none";
                editor.refresh();
            }
        };
        repl_button.onclick = function(event) {
            if (edit_mode === "edit") {
                edit_mode = "repl";
                repl_container.style.display="block";
                editor_container.style.display="none";
            }
        };

        var shift = false;

        editor.setOption("extraKeys", {
            "Shift-Enter": function(cm) { dump_editor();}
        });
        
        vertical_button.onclick();
        return { editor: editor, editor_elt: editor_elt, repl: repl, errors: errors, dump_button: dump_button };
    };

 
    this.new_vm = function() { return new VeneerVM(); };
}
