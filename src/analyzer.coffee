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
  @next = 0
  constructor: (pos) ->
    @pos = [] # do not save pos for now
    @id = ++Constraint.next
  toString: ->
    if @pos.length == 0
      @smt()
    else
      pos = ("#{p.start_offset}-#{p.end_offset}" for p in @pos)
      "(! #{@smt()} :named C_#{@id}_#{pos.join '_'})"

class ObjectConstraint extends Constraint
  constructor: (@node, @objidx, pos) -> super pos
  smt: -> "(hasobj #{@node} O#{@objidx} #{})"

class FunctionConstraint extends Constraint
  constructor: (@node, @funcidx, pos) -> super pos
  smt: -> "(hasfunc #{@node} F#{@funcidx})"

class FlowConstraint extends Constraint
  constructor: (@from, @to, pos) -> super pos
  smt: -> "(flow #{@from} #{@to})"

class FlowRes extends FlowConstraint
  smt: -> "(flow-res #{@from} #{@to})"

class FlowArg extends FlowConstraint
  constructor: (from, to, @argidx, pos) -> super from, to, pos
  smt: -> "(flow-arg #{@from} #{@to} A#{@argidx})"

class FlowGet extends FlowConstraint
  constructor: (from, @propidx, to, pos) -> super from, to, pos
  smt: -> "(flow-get #{@from} S#{@propidx} #{@to})"

class FlowSet extends FlowConstraint
  constructor: (from, to, @propidx, pos) -> super from, to, pos
  smt: -> "(flow-set #{@from} #{@to} S#{@propidx})"

class FlowResConstructor extends FlowConstraint
  smt: -> "(flow-res-cons #{@from} #{@to})"

class FlowThis extends Constraint
  constructor: (@obj, @propidx, pos) -> super pos
  smt: -> "(flow-this #{@obj} S#{@propidx})"

class ProtoConstraint extends Constraint
  constructor: (@fidx, @oidx, pos) -> super pos
  smt: -> "(= (proto F#{@fidx}) O#{@oidx})"

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
    @hasobj (new This 0), 1, []
    super src
    @solve cb

  assigned: (to) ->
    @simpleProps[to] = false

  flow: (from, to, pos) ->
    @constraints.push new FlowConstraint from, to, pos
    @assigned to

  flowRes: (from, to, pos) ->
    @constraints.push new FlowRes from, to, pos
    @assigned to

  flowArg: (arg, func, i, pos) ->
    @constraints.push new FlowArg arg, func, i, pos

  flowGet: (obj, prop, to, pos) ->
    @constraints.push new FlowGet obj, @prop(prop), to, pos
    @assigned to

  flowSet: (from, obj, prop, pos) ->
    @constraints.push new FlowSet from, obj, @prop(prop), pos

  flowResConstructor: (from, to, pos) ->
    @constraints.push new FlowResConstructor from, to, pos

  flowThis: (obj, prop, pos) ->
    @constraints.push new FlowThis obj, @prop(prop), pos

  hasfunc: (x, func, pos) ->
    @constraints.push new FunctionConstraint x, func, pos
    @assigned x

  hasobj: (x, obj, pos) ->
    @constraints.push new ObjectConstraint x, obj, pos
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
  visitFunction: (x, func, pos) ->
    scope = {}
    scope['#f'] = ++@funcs
    @hasobj (new This @funcs), ++@objs, []
    @constraints.push new ProtoConstraint @funcs, @objs, []
    @args = Math.max @args, func.params.length
    for param,i in func.params
      @vars++
      scope[param.name] = @vars
      p = if param.attr.pos then [param.attr.pos] else []
      @flow (new Arg @funcs, i + 1), new Var(@vars), p
    @scopes.push scope
    @visit func.body
    @scopes.pop()
    @hasfunc (@var x), scope['#f'], pos

  # Id
  visitVarDeclaration: (varname, pos) ->
    unless _.last(@scopes).hasOwnProperty varname
      @vars++
      _.last(@scopes)[varname] = @vars

  # Id, Literal
  visitLiteral: (x, lit, pos) ->
    if typeof lit is 'string' and not @simpleProps.hasOwnProperty(@var x)
      @simpleProps[@var x] = @str lit
    else
      @assigned (@var x)

  # Id
  visitThis: (x, pos) ->
    @flow (new This _.last(@scopes)['#f']), (@var x), pos

  # Id, [Id]
  visitArray: (x, arr, pos) ->
    @objs++
    @flow (@var v), (new Prop @objs, 0), [pos[i + 1]] for v, i in arr
    @hasobj (@var x), @objs, [pos[0]]

  # Id, {Id: Id }
  visitObjectLiteral: (x, obj, pos) ->
    @objs++
    @hasobj (@var x), @objs, pos[0]
    @flow (@var v), (new Prop @objs, (@str k)), [pos[1][k]] for k, v of obj

  # Id, Id
  visitVariable: (x, y, pos) ->
    @flow (@var y), (@var x), pos

  # Id, Id, Id
  visitGet: (x, o, f, pos) ->
    @flowGet (@var o), (@var f), (@var x), pos

  # Id, Id, Id
  visitSet: (o, f, y, pos) ->
    @flowSet (@var y), (@var o), (@var f), pos

  # Id, Id
  visitDeleteGlobal: (x, y) -> throw new Error 'not supported'

  # Id, Id, Id
  visitDelete: (x, o, f, pos) ->
    @visitGet x, o, f, pos

  # Id, Op, Id
  visitUnOp: (x, op, a, pos) ->
    @assigned x

  # Id, Id, Op, Id
  visitBinOp: (x, a, op, b, pos) ->
    if op == '||' or op == '&&'
      @flow (@var b), (@var x), pos
    @assigned x

  # Id, Id, [Id]
  visitCall: (x, f, args, pos) ->
    for arg, i in args
      @flowArg (@var arg), (@var f), i + 1, [pos[1], pos[i + 2]]
    @flowRes (@var f), (@var x), [pos[0], pos[1]]

  # Id, Id, Id, [Id]
  visitMethodCall: (x, o, f, args, pos) ->
    for arg,i in args
      @flowArg (@var arg), (@var f), i + 1, [pos[1], pos[2], pos[i + 3]]
    @flowThis (@var o), (@var f), [pos[1], pos[2]]
    @flowRes (@var f), (@var x), [pos[0], pos[1], pos[2]]

  # Id, Id, [Id]
  visitConstructorCall: (x, f, args, pos) ->
    for arg,i in args
      @flowArg (@var arg), (@var f), i + 1, [pos[1], pos[i + 2]]
    @flowResConstructor (@var f), (@var x), [pos[0], pos[1]]

  # Id?
  visitReturn: (x, pos) ->
    @flow (@var x), new Res(_.last(@scopes)['#f']), pos if x

  # Id
  visitBreak: (l, pos) -> # nothing to do

  # Id
  visitThrow: (x, pos) -> throw new Error 'not supported'

  # ()
  visitDebugger: (pos) -> # nothing to do

  # Id, Statement
  visitLabel: (l, s, pos) -> @visit s

  # Id, [Statement], [Statement]
  visitIf: (cond, consequent, alternate, pos) ->
    @visit s for s in consequent
    @visit s for s in alternate

  # Id, [Statement]
  visitWhile: (cond, block, pos) ->
    @visit s for s in block

  # Id, Id, [Statement]
  visitForIn: (x, o, block, pos) ->
    throw new Error 'not supported'
    #TODO what about x and o?
    @visit s for s in block

  # [Statement], Id, [Statement]
  visitTryCatch: (block, x, catchBlock, pos) ->
    throw new Error 'not supported'
    @visit s for s in block
    #TODO what about x?
    @visit s for s in catchBlock

  # [Statement], [Statement]
  visitTryFinally: (block, finallyBlock, pos) ->
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
    fs.readFile "#{__dirname}/../src/constraints.tpl.smt", (err, tpl) =>
      throw err if err
      smt = _(tpl).template @templateData()
      child = exec "#{__dirname}/../z3/build/z3 -smt2 -in", (err, stdout) ->
        lines = stdout.split '\n'
        throw Error('SMT failed') unless /^(un)?sat/.test lines[0]
        if /^sat/.test lines[0]
          cb success: true
        else
          pos = lines[1].substr(1, lines[1].length - 2)
            .split(' ')
            .map (p) -> p.split('_').slice(2)
          pos = [].concat.apply [], pos
          pos = (p.split('-').map((pp) -> +pp) for p in pos)
          pos = ([from, Math.max(from + 4, to)] for [from,to] in pos)
          cb {success: false, pos: pos}
      fs.writeFileSync './tmp.smt', smt
      child.stdin.end smt

Analyzer.Constraint = Constraint

if typeof window != 'undefined'
  window.Analyzer = Analyzer
else
  module.exports = Analyzer
