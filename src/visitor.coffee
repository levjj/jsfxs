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
  visitFunction: (x, func, pos) ->
  # Id
  visitVarDeclaration: (varname, pos) ->
  # Id, Literal
  visitLiteral: (x, lit, pos) ->
  # Id
  visitThis: (x, pos) ->
  # Id, [Id]
  visitArray: (x, arr, pos) ->
  # Id, {Id: Id }
  visitObjectLiteral: (x, obj, pos) ->
  # Id, Id
  visitVariable: (x, y, pos) ->
  # Id, Id, Id
  visitGet: (x, o, f, pos) ->
  # Id, Id, Id
  visitSet: (o, f, y, pos) ->
  # Id, Id
  visitDeleteGlobal: (x, y, pos) ->
  # Id, Id, Id
  visitDelete: (x, o, f, pos) ->
  # Id, Op, Id
  visitUnOp: (x, op, a, pos) ->
  # Id, Id, Op, Id
  visitBinOp: (x, a, op, b, pos) ->
  # Id, Id, [Id]
  visitCall: (x, f, args, pos) ->
  # Id, Id, Id, [Id]
  visitMethodCall: (x, o, f, args, pos) ->
  # Id, Id, [Id]
  visitConstructorCall: (x, f, args, pos) ->
  # Id?
  visitReturn: (x, pos) ->
  # Id
  visitBreak: (l, pos) ->
  # Id
  visitThrow: (x, pos) ->
  # ()
  visitDebugger: (pos) ->
  # Id, Statement
  visitLabel: (l,s,pos) ->
  # Id, [Statement], [Statement]
  visitIf: (cond, consequent, alternate, pos) ->
  # Id, [Statement]
  visitWhile: (cond, block, pos) ->
  # Id, Id, [Statement]
  visitForIn: (x, o, block, pos) ->
  # [Statement], Id, [Statement]
  visitTryCatch: (block, x, catchBlock, pos) ->
  # [Statement], [Statement]
  visitTryFinally: (block, finallyBlock, pos) ->

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
      @visitVarDeclaration '__global', []
      @visitObjectLiteral '__global', {}, [[], {}]
      @visit node.body[0].expression.callee.body
    when 'BlockStatement'
      @visit n for n in node.body
    when 'IfStatement', 'ConditionalExpression'
      @ensureType node.test, 'Identifier'
      @ensureType node.consequent, 'BlockStatement'
      @ensureType node.alternate, 'BlockStatement'
      pos = [node.test.attr.pos]
      @visitIf node.test.name, node.consequent.body, node.alternate.body, pos
    when 'LabeledStatement'
      @visitLabel node.label.name, node.body, []
    when 'EmptyStatement' then # do nothing
    when 'BreakStatement'
      @ensure node.label
      @visitBreak node.label.name, []
    # when "ContinueStatement" then -- desugared to break
    # when 'WithStatement' then -- not supported
    # when 'SwitchStatement' -- desugared
    when 'ReturnStatement'
      if node.argument
        @ensureType node.argument, 'Identifier'
        pos = [node.argument.attr.pos]
      @visitReturn node.argument?.name, pos || []
    when 'ThrowStatement'
      @ensureType node.argument, 'Identifier'
      @visitThrow node.argument.name, []
    when 'TryStatement'
      if node.handler
        @nsure !node.finalizer
        @visitTryCatch node.block, node.handler.param.name, node.handler.body,[]
      else
        @visitTryFinally node.block, node.finalizer, []
    when 'WhileStatement'
      @ensureType node.test, 'Identifier'
      @ensureType node.body, 'BlockStatement'
      @visitWhile node.test.name, node.body.body, [node.test.attr.pos]
    #when "DoWhileStatement" then -- desugared to while
    #when "ForStatement" then -- desugared to while
    when 'ForInStatement'
      @ensureType node.left, 'Identifier'
      @ensureType node.right, 'Identifier'
      @ensureType node.body, 'BlockStatement'
      pos = [node.left.attr.pos, node.right.attr.pos]
      @visitForIn node.left.name, node.right.name, node.body.body, pos
    # when 'ForOfStatement' then -- not supported
    # when 'LetStatement' then -- not supported
    when 'DebuggerStatement'
      @visitDebugger [node.attr.pos]
    when 'VariableDeclaration'
      for decl in node.declarations
        @ensure !decl.init
        @visitVarDeclaration decl.id.name, []
    when 'ExpressionStatement'
      @ensureType node.expression, 'AssignmentExpression'
      left = node.expression.left
      right = node.expression.right
      if node.expression.left.type == 'MemberExpression'
        @ensureType left.object, 'Identifier'
        @ensureType left.property, 'Identifier'
        @ensure left.computed
        @ensureType right, 'Identifier'
        pos = [left.object.attr.pos, left.property.attr.pos, right.attr.pos]
        return @visitSet left.object.name, left.property.name, right.name, pos
      @ensureType left, 'Identifier'
      pleft = left.attr.pos
      left = left.name
      switch right.type
        when 'FunctionExpression'
          @visitFunction left, right, [pleft]
        when 'ThisExpression'
          @visitThis left, [pleft, right.attr.pos]
        when 'ArrayExpression'
          @ensureType e, 'Identifier' for e in right.elements
          @visitArray left,
            (e.name for e in right.elements),
            _.union([pleft], (e.attr.pos for e in right.elements))
        when 'ObjectExpression'
          props = {}
          pos = {}
          for prop in right.properties
            @ensure prop.kind == 'init'
            @ensureType prop.value, 'Identifier'
            props[prop.key.name] = prop.value.name
            pos[prop.key.name] = prop.value.attr.pos
          @visitObjectLiteral left, props, [[pleft], pos]
        # when 'SequenceExpression' then # -- desugared
        when 'UnaryExpression'
          if right.operator == 'delete'
            right = right.argument
            if right.type == 'MemberExpression'
              @ensureType right.object, 'Identifier'
              @ensureType right.property, 'Identifier'
              @ensure right.computed
              @visitDelete left, right.object.name, right.property.name, [pleft]
            else
              @ensureType right, 'Identifier'
              @visitDeleteGlobal left, right, [pleft]
          else
            @ensureType right.argument, 'Identifier'
            pos = [pleft, right.argument.attr.pos]
            @visitUnOp left, right.operator, right.argument.name, pos
        when 'BinaryExpression'
          @ensureType right.left, 'Identifier'
          @ensureType right.right, 'Identifier'
          pos = [pleft, right.left.attr.pos, right.right.attr.pos]
          @visitUnOp left, right.left.name, right.right.name, pos
        # when 'UpdateExpression' then # -- desugared
        # when 'LogicalExpression' then # -- desugared
        when 'CallExpression', 'NewExpression'
          @ensureType a, 'Identifier' for a in right.arguments
          args = (a.name for a in right.arguments)
          pos = _.union [pleft], (a.attr.pos for a in right.arguments)
          callee = right.callee
          if right.type == 'CallExpression' && callee.type == 'MemberExpression'
            @ensureType callee.object, 'Identifier'
            @ensureType callee.property, 'Identifier'
            @ensure callee.computed
            pos.unshift callee.property.attr.pos
            pos.unshift callee.object.attr.pos
            @visitMethodCall left,
                             callee.object.name,
                             callee.property.name,
                             args,
                             pos
          else
            @ensureType callee, 'Identifier'
            pos.unshift callee.attr.pos
            if right.type == 'NewExpression'
              @visitConstructorCall left, callee.name, args, pos
            else
              @visitCall left, callee.name, args, pos
        when 'MemberExpression'
          @ensureType right.object, 'Identifier'
          @ensureType right.property, 'Identifier'
          @ensure right.computed
          pos = [pleft, right.object.attr.pos, right.property.attr.pos]
          @visitGet left, right.object.name, right.property.name, pos
        # when 'YieldExpression' then -- not supported
        # when 'ComprehensionExpression' then -- not supported
        # when 'GeneratorExpression' then -- not supported
        when 'Identifier'
          @visitVariable left, right.name, [pleft, right.attr.pos]
        when 'Literal'
          @visitLiteral left, right.value, [pleft, right.attr.pos]
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
