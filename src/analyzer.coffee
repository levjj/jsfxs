esprima = require 'esprima'
normalizer = require 'JS_WALA/normalizer/lib/normalizer'
escodegen = require 'escodegen'
_ = require 'lodash'
if typeof window == 'undefined'
  fs = require 'fs'
  exec = require('child_process').exec

class Analyzer

  parse: (src) ->
    @ast = esprima.parse src, {loc: true, range: true}

  normalize: ->
    @ast = normalizer.normalize @ast,
      reference_errors: true
      unify_ret: true

  codegen: ->
    {code,map} = escodegen.generate @ast,
      sourceMap: 'foo'
      sourceMapWithCode: true
    code

  validate: (src,cb) ->
    @parse src
    @normalize()
    @analyze()
    @solve cb

  analyze: ->
    @funcs = []
    @objs = []
    @objConstraints = []
    @funcConstraints = []
    @flowConstraints = []
    @f @ast

  addFunc: (node) ->
    id = "f#{1+@funcs.length}"
    @funcs.push id
    id

  addObj: (node) ->
    id = "o#{1+@objs.length}"
    @objs.push id
    id

  f: (node) -> return unless node ; switch node.type
    when 'Program', 'BlockStatement'
      @f n for n in node.body
    when 'ExpressionStatement'
      @f node.expression
    when 'IfStatement', 'ConditionalExpression'
      @f node.test
      @f node.consequent
      @f node.alternate
    when 'LabeledStatement'
      @f node.body
    when 'EmptyStatement' then # do nothing
    when 'BreakStatement' then # always has label
    #when "ContinueStatement" then # -- desugared to break
    when 'WithStatement' then throw Error 'with not supported'
    when 'SwitchStatement'
      @f node.discriminant
      @f caze for caze in node.cases
    when 'SwitchCase'
      @f node.test
      @f node.consequent
    when 'ReturnStatement'
      @f node.argument
    when 'ThrowStatement'
      @f node.argument
    when 'TryStatement'
      @f node.block
      @f node.handler
      @f handler for handler in node.guardedHandlers
      @f node.finalizer
    when 'CatchClause'
      @f node.guard
      @f node.body
    when 'WhileStatement'
      @f node.test
      @f node.body
    #when "DoWhileStatement" then # -- desugared to while
    #when "ForStatement" then # -- desugared to while
    when 'ForInStatement'
      @f node.left
      @f node.right
      @f node.body
    when 'ForOfStatement' then throw Error 'for of not supported'
    when 'LetStatement' then throw Error 'let not supported'
    when 'DebuggerStatement' then throw Error 'debugger not supported'
    when 'FunctionDeclaration', 'FunctionExpression', 'ArrowExpression'
      @addFunc node
      @addObj node
      if node.defaults
        @f def for def in node.defaults
      @f node.body
    when 'VariableDeclaration'
      @f decl for decl in node.declarations
    when 'VariableDeclarator'
      @f node.init
    when 'ThisExpression' then # do nothing
    when 'ArrayExpression'
      if node.elements
        @f e for e in node.elements
    when 'ObjectExpression'
      @addObj node
      @f prop for prop in node.properties
    when 'Property'
      @f node.value
    when 'SequenceExpression'
      @f expr for expr in node.expressions
    when 'UnaryExpression'
      @f node.argument
    when 'BinaryExpression'
      @f node.left
      @f node.right
    when 'AssignmentExpression'
      @f node.left
      @f node.right
    when 'UpdateExpression'
      @f node.argument
    when 'LogicalExpression'
      @f node.left
      @f node.right
    when 'CallExpression', 'NewExpression'
      @f node.callee
      @f arg for arg in node.arguments
    when 'MemberExpression'
      @f node.object
      @f node.property if node.computed
    when 'YieldExpression' then throw Error 'yield not supported'
    when 'ComprehensionExpression' then throw Error 'compreh. not supported'
    when 'GeneratorExpression' then throw Error 'generators not supported'
    when 'Identifier' then # do nothing
    when 'Literal' then # do nothing
    else
      throw Error 'Unknown AST node'

  solve: (cb) ->
    @result = []
    fs.readFile './src/constraints.tpl.smt', (err, tpl) =>
      throw err if err
      smt = _(tpl).template
        nodes: ['n1', 'n2', 'n3']
        funcs: @funcs
        objs: @objs
        objConstraints: @objConstraints
        funcConstraints: @funcConstraints
        flowConstraints: @flowConstraints
      child = exec 'cvc4 -L smt2', (err, stdout, stderr) =>
        throw Error('SMT failed') unless /^(un)?sat/.test stdout
        @result = /^sat/.test stdout
        cb @result
      child.stdin.end smt

if typeof window != 'undefined'
  window.Analyzer = Analyzer
else
  module.exports = Analyzer
