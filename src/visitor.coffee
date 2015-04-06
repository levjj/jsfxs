esprima = require 'esprima'
normalizer = require 'JS_WALA/normalizer/lib/normalizer'
escodegen = require 'escodegen'
_ = require 'lodash'

class Visitor
  parse: (src) ->
    @ast = esprima.parse src, {loc: true, range: true}

  normalize: ->
    @ast = normalizer.normalize @ast,
      unify_ret: true

  codegen: ->
    {code,map} = escodegen.generate @ast,
      sourceMap: 'foo'
      sourceMapWithCode: true
    code

  # Id, Function
  visitFunction: (x, func) ->
  # Id
  visitVarDeclaration: (varname) ->
  # Id, Literal
  visitLiteral: (x, lit) ->
  # Id
  visitThis: (x) ->
  # Id, [Id]
  visitArray: (x, arr) ->
  # Id, {Id: Id }
  visitObjectLiteral: (x, obj) ->
  # Id, Id
  visitVariable: (x, y) ->
  # Id, Id, Id
  visitGet: (x, o, f) ->
  # Id, Id, Id
  visitSet: (o, f, y) ->
  # Id, Id
  visitDeleteGlobal: (x, y) ->
  # Id, Id, Id
  visitDelete: (x, o, f) ->
  # Id, Op, Id
  visitUnOp: (x, op, a) ->
  # Id, Id, Op, Id
  visitBinOp: (x, a, op, b) ->
  # Id, Id, [Id]
  visitCall: (x, f, args) ->
  # Id, Id, Id, [Id]
  visitMethodCall: (x, o, f, args) ->
  # Id, Id, [Id]
  visitConstructorCall: (x, f, args) ->
  # Id?
  visitReturn: (x) ->
  # Id
  visitBreak: (l) ->
  # Id
  visitThrow: (x) ->
  # ()
  visitDebugger: ->
  # Id, Statement
  visitLabel: (l,s) ->
  # Id, [Statement], [Statement]
  visitIf: (cond, consequent, alternate) ->
  # Id, [Statement]
  visitWhile: (cond, block) ->
  # Id, Id, [Statement]
  visitForIn: (x, o, block) ->
  # [Statement], Id, [Statement]
  visitTryCatch: (block, x, catchBlock) ->
  # [Statement], [Statement]
  visitTryFinally: (block, finallyBlock) ->

  ensure: (cond, msg = 'Expected true') ->
    throw new Error msg unless !!cond

  ensureType: (node, type) ->
    @ensure (node.type == type), "#{node.type} was expected to be #{type}"

  visit: (node) -> return unless node ; switch node.type
    when 'Program'
      @ensure node.body.length == 1
      @ensureType node.body[0], 'ExpressionStatement'
      @ensureType node.body[0].expression, 'CallExpression'
      @ensureType node.body[0].expression.callee, 'FunctionExpression'
      @visitVarDeclaration '__global'
      @visitObjectLiteral '__global', {}
      @visit node.body[0].expression.callee.body
    when 'BlockStatement'
      @visit n for n in node.body
    when 'IfStatement', 'ConditionalExpression'
      @ensureType node.test, 'Identifier'
      @ensureType node.consequent, 'BlockStatement'
      @ensureType node.alternate, 'BlockStatement'
      @visitIf node.test.name, node.consequent.body, node.alternate.body
    when 'LabeledStatement'
      @visitLabel node.label.name, node.body
    when 'EmptyStatement' then # do nothing
    when 'BreakStatement'
      @ensure node.label
      @visitBreak node.label.name
    # when "ContinueStatement" then -- desugared to break
    # when 'WithStatement' then -- not supported
    # when 'SwitchStatement' -- desugared
    when 'ReturnStatement'
      @ensureType node.argument, 'Identifier' if node.argument
      @visitReturn node.argument?.name
    when 'ThrowStatement'
      @ensureType node.argument, 'Identifier'
      @visitThrow node.argument.name
    when 'TryStatement'
      if node.handler
        @nsure !node.finalizer
        @visitTryCatch node.block, node.handler.param.name, node.handler.body
      else
        @visitTryFinally node.block, node.finalizer
    when 'WhileStatement'
      @ensureType node.test, 'Identifier'
      @ensureType node.body, 'BlockStatement'
      @visitWhile node.test.name, node.body.body
    #when "DoWhileStatement" then -- desugared to while
    #when "ForStatement" then -- desugared to while
    when 'ForInStatement'
      @ensureType node.left, 'Identifier'
      @ensureType node.right, 'Identifier'
      @ensureType node.body, 'BlockStatement'
      @visitForIn node.left.name, node.right.name, node.body.body
    # when 'ForOfStatement' then -- not supported
    # when 'LetStatement' then -- not supported
    when 'DebuggerStatement'
      @visitDebugger()
    when 'VariableDeclaration'
      for decl in node.declarations
        @ensure !decl.init
        @visitVarDeclaration decl.id.name
    when 'ExpressionStatement'
      @ensureType node.expression, 'AssignmentExpression'
      left = node.expression.left
      right = node.expression.right
      if node.expression.left.type == 'MemberExpression'
        @ensureType left.object, 'Identifier'
        @ensureType left.property, 'Identifier'
        @ensure left.computed
        @ensureType right, 'Identifier'
        return @visitSet left.object.name, left.property.name, right.name
      @ensureType left, 'Identifier'
      left = left.name
      switch right.type
        when 'FunctionExpression'
          @visitFunction left, right
        when 'ThisExpression'
          @visitThis left
        when 'ArrayExpression'
          @ensureType e, 'Identifier' for e in right.elements
          @visitArray left, (e.name for e in right.elements)
        when 'ObjectExpression'
          props = {}
          for prop in right.properties
            @ensure prop.kind == 'init'
            @ensureType prop.value, 'Identifier'
            props[prop.key.name] = prop.value.name
          @visitObjectLiteral left, props
        # when 'SequenceExpression' then # -- desugared
        when 'UnaryExpression'
          if right.operator == 'delete'
            right = right.argument
            if right.type == 'MemberExpression'
              @ensureType right.object, 'Identifier'
              @ensureType right.property, 'Identifier'
              @ensure right.computed
              @visitDelete left, right.object.name, right.property.name
            else
              @ensureType right, 'Identifier'
              @visitDeleteGlobal left, right
          else
            @ensureType right.argument, 'Identifier'
            @visitUnOp left, right.operator, right.argument.name
        when 'BinaryExpression'
          @ensureType right.left, 'Identifier'
          @ensureType right.right, 'Identifier'
          @visitUnOp left, right.left.name, right.right.name
        # when 'UpdateExpression' then # -- desugared
        # when 'LogicalExpression' then # -- desugared
        when 'CallExpression', 'NewExpression'
          @ensureType a, 'Identifier' for a in right.arguments
          args = (a.name for a in right.arguments)
          callee = right.callee
          if right.type == 'CallExpression' && callee.type == 'MemberExpression'
            @ensureType callee.object, 'Identifier'
            @ensureType callee.property, 'Identifier'
            @ensure callee.computed
            @visitMethodCall left,
                             callee.object.name,
                             callee.property.name,
                             args
          else
            @ensureType callee, 'Identifier'
            if right.type == 'NewExpression'
              @visitConstructorCall left, callee.name, args
            else
              @visitCall left, callee.name, args
        when 'MemberExpression'
          @ensureType right.object, 'Identifier'
          @ensureType right.property, 'Identifier'
          @ensure right.computed
          @visitGet left, right.object.name, right.property.name
        # when 'YieldExpression' then -- not supported
        # when 'ComprehensionExpression' then -- not supported
        # when 'GeneratorExpression' then -- not supported
        when 'Identifier'
          @visitVariable left, right.name
        when 'Literal'
          @visitLiteral left, right.value
        else
          throw new Error 'Unknown AST node in expression'
    else
      throw new Error 'Unknown AST node in statement'

  run: (src) ->
    @parse src
    @normalize()
    @visit @ast

if typeof window != 'undefined'
  window.Visitor = Visitor
else
  module.exports = Visitor
