define("ace/snippets/anchor",["require","exports","module"], function(require, exports, module) {
"use strict";

exports.snippetText = "snippet /stack\n\
\n\
	class Node {\n\
	  int item  moves_as isLocal(this) ? threadlocal : readonly;\n\
	  Node next moves_as isLocal(this) ? threadlocal : readonly;\n\
\n\
	  Node(int item, Node next) {\n\
	    this.item = item;\n\
	    this.next = next;\n\
	  }\n\
	}\n\
	\n\
	\n\
\n\
\n\
\n\
\n\
\n\
	class Stack {\n\
\n\
	  Node head;\n\
\n\
	  public void push(int item) {\n\
	    acquire(this);\n\
	    Node node = new Node(item, this.head);\n\
	    this.head = node;\n\
	    release(this);\n\
	  }\n\
	}\n\
\n\
\n\
\n\
\n\
\n\
\n\
\n\
\n\
\n\
\n\
\n\
\n\
\n\
\n\
\n\
snippet /pop\n\
	  public int pop() {\n\
	    acquire(this);\n\
	    while (this.head == null) \n\
	      invariant holds(this); {\n\
	      release(this);\n\
	      acquire(this);\n\
	    }\n\
	    int value = this.head.item;\n\
	    this.head = this.head.next;\n\
	    release(this);\n\
	    return value;\n\
	  }\n\
\n\
\n\
snippet /buggy\n\
	public void buggy() {\n\
	  this.push(10);\n\
	  assert this.head.item == 10;\n\
	}\n\
\n\
snippet /pushspec\n\
	modifies this;\n\
	ensures this.head.next == old(this.head); \n\
	ensures this.head.item == item;\n\
\n\
snippet /popspec\n\
	modifies this;\n\
	ensures old(this.head) != null;\n\
	ensures $result == old(this.head.item); \n\
	ensures this.head == old(this.head.next);\n\
";
exports.scope = "anchor";

});                (function() {
                    window.require(["ace/snippets/anchor"], function(m) {
                        if (typeof module == "object" && typeof exports == "object" && module) {
                            module.exports = m;
                        }
                    });
                })();
            