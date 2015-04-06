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
  constructor: (@oidx, @pidx) ->
  toString: -> "(Prop O#{@oidx} P#{@pidx})"

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
  toString: -> "(flow-get #{@from} P#{@propidx} #{@to})"

class FlowSet extends FlowConstraint
  constructor: (from, @propidx, to) -> super from, to
  toString: -> "(flow-get #{@from} P#{@propidx} #{@to})"

class Analyzer extends Visitor
  run: (src,cb) ->
    @funcs = 0
    @objs = 0
    @vars = 0
    @props = 0
    @args = 0
    @constraints = []
    @scopes = [{}]
    @propNames = {}
    super src
    @solve cb

  flow: (from, to) ->
    @constraints.push new FlowConstraint from, to

  var: (varname) ->
    lookup = (scopes) ->
      if _.last(scopes).hasOwnProperty varname
        return new Var _.last(scopes)[varname]
      lookup _.initial scopes
    lookup @scopes

  prop: (objidx, propname) ->
    unless @propNames.hasOwnProperty propname
      @propNames[propname] = ++@props
    Obj objidx, @propNames[propname]

  # Id, Function
  visitFunction: (x, func) ->
    @funcs++
    #@objs++  -- TODO add support for new
    scope = {}
    scope['#f'] = @funcs
    @args = Math.max @args, func.params.length
    for param in func.params
      @vars++
      scope[param.name] = @vars
    @scopes.push scope
    @visit func.body
    @scopes.pop()
    @constraints.push new FunctionConstraint((@var x), @funcs)

  # Id
  visitVarDeclaration: (varname) ->
    unless _.last(@scopes).hasOwnProperty varname
      @vars++
      _.last(@scopes)[varname] = @vars

  # Id, Literal
  visitLiteral: (x, lit) ->

  # Id
  visitThis: (x) -> throw new Error 'not supported'

  # Id, [Id]
  visitArray: (x, arr) -> throw new Error 'not supported'

  # Id, {Id: Id }
  visitObjectLiteral: (x, obj) ->
    return
    throw new Error 'not supported'
    @objs++
    @flow (@var v) (@prop @objs, k) for k, v of obj
    @constraints.push new ObjectConstraint((@var x), @objs)

  # Id, Id
  visitVariable: (x, y) ->
    @flow (@var y), (@var x)

  # Id, Id, Id
  visitGet: (x, o, f) ->
    throw new Error 'not supported'
    # ------------
    @flow (@prop o, f), (@var x)

  # Id, Id, Id
  visitSet: (o, f, y) -> throw new Error 'not supported'

  # Id, Id
  visitDeleteGlobal: (x, y) -> throw new Error 'not supported'

  # Id, Id, Id
  visitDelete: (x, o, f) -> throw new Error 'not supported'

  # Id, Op, Id
  visitUnOp: (x, op, a) -> # nothing to do

  # Id, Id, Op, Id
  visitBinOp: (x, a, op, b) ->
    if op == '||' or op == '&&'
      @flow (@var b), (@var x)

  # Id, Id, [Id]
  visitCall: (x, f, args) ->
    for arg,i in args
      @constraints.push new FlowArg (@var arg), (@var f), i + 1
    @constraints.push new FlowRes (@var f), (@var x)

  # Id, Id, Id, [Id]
  visitMethodCall: (x, o, f, args) -> throw new Error 'not supported'

  # Id, Id, [Id]
  visitConstructorCall: (x, f, args) -> throw new Error 'not supported'

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

  solve: (cb) ->
    @result = []
    fs.readFile './src/constraints.tpl.smt', (err, tpl) =>
      throw err if err
      smt = _(tpl).template
        funcs: @funcs || 1
        objs: @objs || 1
        vars: @vars || 1
        props: @props || 1
        args: @args || 1
        constraints: @constraints
      child = exec 'cvc4 -L smt2', (err, stdout, stderr) =>
        throw Error('SMT failed') unless /^(un)?sat/.test stdout
        @result = /^sat/.test stdout
        cb @result
      fs.writeFileSync './tmp.smt', smt
      child.stdin.end smt

if typeof window != 'undefined'
  window.Analyzer = Analyzer
else
  module.exports = Analyzer
