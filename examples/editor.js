function load_editor() {
    var veneer = new Veneer_v1();

    var vm = veneer.new_vm();

    var ed = veneer.new_editor(document.getElementById("container"), vm);
    var editor = ed.editor;
    var editor_elt = ed.editor_elt;
    var repl = ed.repl;
    var errors = ed.errors;
    var dump_button = ed.dump_button;


    var font_size = 10;
    var font_plus = document.getElementById("font_plus");
    var font_minus = document.getElementById("font_minus");
    font_plus.onclick = function() {
        font_size = font_size + 1;
        editor_elt.style.fontSize = "" + font_size + "pt";
        repl.style.fontSize = "" + font_size + "pt";
        editor.refresh()
    };
    font_minus.onclick = function() {
        font_size = font_size - 1;
        repl.style.fontSize = "" + font_size + "pt";
        editor_elt.style.fontSize = "" + font_size + "pt";
        editor.refresh();
    };

    var slider = document.getElementById("slider");
    slider.onchange = function() {
        font_size = (parseInt(slider.value) + 16) * 0.5;
        editor_elt.style.fontSize = "" + font_size + "pt";
        repl.style.fontSize = "" + font_size + "pt";
        editor.refresh();
    };

    var demo = false;
    function setEditorValue(val) {
        demo = false;
        editor.setValue(val);
    }

    var demos = document.getElementsByClassName("demo");
    var demo_picker = document.getElementById("demo_picker");
    var file_values = new Array(demos.length);
    for(var i=0; i < demos.length; i++ ) {
        var selection = document.createElement("option");
        var name = demos[i].getElementsByClassName("title")[0].textContent;
        file_values[i] = demos[i].getElementsByClassName("content")[0].value;
        selection.value = i;
        selection.appendChild(document.createTextNode(name));
        demo_picker.appendChild(selection);
    }
    demo_picker.onchange = function() {
        load_demo(demo_picker.selectedIndex);
    };
    demo_picker.value = "0";
    setEditorValue(file_values[0]);
    demo = 0;

    document.getElementById("create_link").onclick = function() {
        var req = new XMLHttpRequest();
        var method = "POST";
        var url = "https://api.github.com/gists";

        var options = {
            "description": "veneer save",
            "public": true,
            "files": {
                "file": {
                    "content": editor.getValue()
                }
            }
        };

        req.open(method, url, true);
        req.onreadystatechange = function () {
            if (req.readyState !== XMLHttpRequest.DONE) {
                return;
            }
            if (req.status === 201) {
                var response = JSON.parse(req.responseText);
                window.location.hash = response.id;
            }
        };
        req.send(JSON.stringify(options));
    };

    function load_demo(id) {
        var save_status = true;
        if(save_status) {
            var demo_val = file_values[id];
            setEditorValue(demo_val);
            demo = id;
        }
    }

    if(window.location.hash) {
        var req = new XMLHttpRequest();
        var method = "GET";
        var url = "https://api.github.com/gists/" + window.location.hash.substring(1);

        req.open(method, url, true);
        req.onreadystatechange = function () {
            if (req.readyState !== XMLHttpRequest.DONE) {
                return;
            }
            if (req.status === 200) {
                var response = JSON.parse(req.responseText);
                setEditorValue(response.files.file.content);
            }
        };
        req.send();
    }
}
