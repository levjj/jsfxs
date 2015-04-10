JSFX - Effect Contracts for Java Script
=======================================

Add effect contracts to your JavaScript and statically check that they can
never be violated.

 * [Online demo](https://livoris.net/jsfx/)

Installation
------------

Install required libraries:

    npm install
    bower install

Install z3:

    git submodule init
    cd z3 ; ./configure ; make

Start server with:

    grunt dist
    grunt serve

Documentation
-------------

Add effect to your JavaScript functions by adding the `fx` keyword and a
list of effect tags/names in square brackets:

```javascript
function alert() fx[dom] { ... }

function fileOpen(fname) fx[io] { ... }
```

Add contracts to arguments of JavaScript functions by adding the `fx` keyword and a
list of non-effect tags/names in square brackets.


```javascript
function startWorker(func fx[!dom,!io]) { ... }

function update(renderFunc fx[!io]) { ... }
```

Use JSFX to analyze the code and find all 

Limitations
-----------

A sound and complete anlaysis in the presence of aliasing, objects and closures
is undecidable, so JSFX overestimates effects.  For example, JSFX reports a
contract violation in the 

```javascript
startWorker(function() {
    if (false) alert();
});
```

Source location highlighted in the editor are sometimes inaccurate partly due
to sweet.js and JS_WALA.

No support for meta-programming constructs like

 * arguments
 * call/apply
 * eval
 * with

No support for ES6 getters and setters.

Flow constraints from `throw` to `catch` is still missing which could cause the
static analysis to miss certain cases.

No support for prototypical inheritance, yet.
