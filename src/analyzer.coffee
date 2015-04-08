_ = require 'lodash'
if typeof window == 'undefined'
  fs = require 'fs'
  exec = require('child_process').exec

Visitor = require './visitor'

class Node

class Var extends Node
  constructor: (@idx) ->
  toString: -> "(Var V#{@idx})"

class Res extends Node
  constructor: (@idx) ->
  toString: -> "(Res F#{@idx})"

class Arg extends Node
  constructor: (@fidx, @aidx) ->
  toString: -> "(Arg F#{@fidx} A#{@aidx})"

class Prop extends Node
  constructor: (@oidx, @sidx) ->
  toString: -> "(Prop O#{@oidx} S#{@sidx})"

class This extends Node
  constructor: (@fidx) ->
  toString: -> "(This F#{@fidx})"

class Constraint

class ObjectConstraint extends Constraint
  constructor: (@node, @objidx) ->
  toString: -> "(hasobj #{@node} O#{@objidx})"

class FunctionConstraint extends Constraint
  constructor: (@node, @funcidx) ->
  toString: -> "(hasfunc #{@node} F#{@funcidx})"

class FlowConstraint extends Constraint
  constructor: (@from, @to) ->
  toString: -> "(flow #{@from} #{@to})"

class FlowRes extends FlowConstraint
  toString: -> "(flow-res #{@from} #{@to})"

class FlowArg extends FlowConstraint
  constructor: (from, to, @argidx) -> super from, to
  toString: -> "(flow-arg #{@from} #{@to} A#{@argidx})"

class FlowGet extends FlowConstraint
  constructor: (from, @propidx, to) -> super from, to
  toString: -> "(flow-get #{@from} S#{@propidx} #{@to})"

class FlowSet extends FlowConstraint
  constructor: (from, to, @propidx) -> super from, to
  toString: -> "(flow-set #{@from} #{@to} S#{@propidx})"

class FlowResConstructor extends FlowConstraint
  toString: -> "(flow-res-cons #{@from} #{@to})"

class FlowThis extends Constraint
  constructor: (@obj, @propidx) ->
  toString: -> "(flow-this #{@obj} S#{@propidx})"

class ProtoConstraint extends Constraint
  constructor: (@fidx, @oidx) ->
  toString: -> "(= (proto F#{@fidx}) O#{@oidx})"

class Analyzer extends Visitor
  run: (src,cb) ->
    @funcs = 0
    @objs = 0
    @vars = 0
    @strs = 0
    @args = 0
    @constraints = []
    @scopes = [{'#f': 0}]
    @strNames = {}
    @simpleProps = {}
    @hasobj (new This 0), 1
    super src
    @solve cb

  assigned: (to) ->
    @simpleProps[to] = false

  flow: (from, to) ->
    @constraints.push new FlowConstraint from, to
    @assigned to

  flowRes: (from, to) ->
    @constraints.push new FlowRes from, to
    @assigned to

  flowArg: (arg, func, i) ->
    @constraints.push new FlowArg arg, func, i

  flowGet: (obj, prop, to) ->
    @constraints.push new FlowGet obj, @prop(prop), to
    @assigned to

  flowSet: (from, obj, prop) ->
    @constraints.push new FlowSet from, obj, @prop(prop)

  flowResConstructor: (from, to) ->
    @constraints.push new FlowResConstructor from, to

  flowThis: (obj, prop) ->
    @constraints.push new FlowThis obj, @prop(prop)

  hasfunc: (x, func) ->
    @constraints.push new FunctionConstraint x, func
    @assigned x

  hasobj: (x, obj) ->
    @constraints.push new ObjectConstraint x, obj
    @assigned x

  var: (varname) ->
    lookup = (scopes) ->
      throw new Error "unknown id #{varname}" if scopes.length == 0
      if _.last(scopes).hasOwnProperty varname
        return new Var _.last(scopes)[varname]
      lookup _.initial scopes
    lookup @scopes

  str: (str) ->
    unless @strNames.hasOwnProperty str
      @strNames[str] = ++@strs
    @strNames[str]

  prop: (p) ->
    if @simpleProps[p]
      @simpleProps[p]
    else
      0

  # Id, Function
  visitFunction: (x, func) ->
    scope = {}
    scope['#f'] = ++@funcs
    @hasobj (new This @funcs), ++@objs
    @constraints.push new ProtoConstraint @funcs, @objs
    @args = Math.max @args, func.params.length
    for param,i in func.params
      @vars++
      scope[param.name] = @vars
      @flow (new Arg @funcs, i + 1), new Var @vars
    @scopes.push scope
    @visit func.body
    @scopes.pop()
    @hasfunc (@var x), scope['#f']

  # Id
  visitVarDeclaration: (varname) ->
    unless _.last(@scopes).hasOwnProperty varname
      @vars++
      _.last(@scopes)[varname] = @vars

  # Id, Literal
  visitLiteral: (x, lit) ->
    if typeof lit is 'string' and not @simpleProps.hasOwnProperty(@var x)
      @simpleProps[@var x] = @str lit
    else
      @assigned (@var x)

  # Id
  visitThis: (x) ->
    @flow (new This _.last(@scopes)['#f']), (@var x)

  # Id, [Id]
  visitArray: (x, arr) ->
    @objs++
    @flow (@var v), (new Prop @objs, 0) for v in arr
    @hasobj (@var x), @objs

  # Id, {Id: Id }
  visitObjectLiteral: (x, obj) ->
    @objs++
    @flow (@var v), (new Prop @objs, (@str k)) for k, v of obj
    @hasobj (@var x), @objs

  # Id, Id
  visitVariable: (x, y) ->
    @flow (@var y), (@var x)

  # Id, Id, Id
  visitGet: (x, o, f) ->
    @flowGet (@var o), (@var f), (@var x)

  # Id, Id, Id
  visitSet: (o, f, y) ->
    @flowSet (@var y), (@var o), (@var f)

  # Id, Id
  visitDeleteGlobal: (x, y) -> throw new Error 'not supported'

  # Id, Id, Id
  visitDelete: (x, o, f) ->
    @visitGet x, o, f

  # Id, Op, Id
  visitUnOp: (x, op, a) ->
    @assigned x

  # Id, Id, Op, Id
  visitBinOp: (x, a, op, b) ->
    if op == '||' or op == '&&'
      @flow (@var b), (@var x)
    @assigned x

  # Id, Id, [Id]
  visitCall: (x, f, args) ->
    for arg,i in args
      @flowArg (@var arg), (@var f), i + 1
    @flowRes (@var f), (@var x)

  # Id, Id, Id, [Id]
  visitMethodCall: (x, o, f, args) ->
    for arg,i in args
      @flowArg (@var arg), (@var f), i + 1
    @flowThis (@var o), (@var f)
    @flowRes (@var f), (@var x)

  # Id, Id, [Id]
  visitConstructorCall: (x, f, args) ->
    for arg,i in args
      @flowArg (@var arg), (@var f), i + 1
    @flowResConstructor (@var f), (@var x)

  # Id?
  visitReturn: (x) ->
    @flow (@var x), new Res _.last(@scopes)['#f'] if x

  # Id
  visitBreak: (l) -> # nothing to do

  # Id
  visitThrow: (x) -> throw new Error 'not supported'

  # ()
  visitDebugger: -> # nothing to do

  # Id, Statement
  visitLabel: (l,s) -> @visit s

  # Id, [Statement], [Statement]
  visitIf: (cond, consequent, alternate) ->
    @visit s for s in consequent
    @visit s for s in alternate

  # Id, [Statement]
  visitWhile: (cond, block) ->
    @visit s for s in block

  # Id, Id, [Statement]
  visitForIn: (x, o, block) ->
    throw new Error 'not supported'
    #TODO what about x and o?
    @visit s for s in block

  # [Statement], Id, [Statement]
  visitTryCatch: (block, x, catchBlock) ->
    throw new Error 'not supported'
    @visit s for s in block
    #TODO what about x?
    @visit s for s in catchBlock

  # [Statement], [Statement]
  visitTryFinally: (block, finallyBlock) ->
    @visit s for s in block
    @visit s for s in finallyBlock

  templateData: ->
    funcs: @funcs || 1
    objs: @objs || 1
    vars: @vars || 1
    strs: @strs || 1
    args: @args || 1
    fxs: 1
    constraints: @constraints

  solve: (cb) ->
    @result = []
    fs.readFile './src/constraints.tpl.smt', (err, tpl) =>
      throw err if err
      smt = _(tpl).template @templateData()
      child = exec 'z3/build/z3 -smt2 -in', (err, stdout, stderr) =>
        throw Error('SMT failed') unless /^(un)?sat/.test stdout
        @result = /^sat/.test stdout
        cb @result
      fs.writeFileSync './tmp.smt', smt
      fs.writeFileSync './tmp.js', @codegen()
      child.stdin.end smt

if typeof window != 'undefined'
  window.Analyzer = Analyzer
else
  module.exports = Analyzer
