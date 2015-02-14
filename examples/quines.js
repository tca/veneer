function load_page() {
    var rel_interp = document.getElementById("rel_interp").value;
    var veneer = new Veneer_v1();
    
    var vm1 = veneer.new_vm();
    var vm2 = veneer.new_vm();
    var vm3 = veneer.new_vm();
    var editor1 = veneer.new_editor(document.getElementById("ed1"), vm1, rel_interp);
    var editor2 = veneer.new_editor(document.getElementById("ed2"), vm2, rel_interp);
    var editor3 = veneer.new_editor(document.getElementById("ed3"), vm3, rel_interp);

    editor1.editor.setValue(document.getElementById("code1").value);
    editor2.editor.setValue(document.getElementById("code2").value);
    editor3.editor.setValue(document.getElementById("code3").value);
}

