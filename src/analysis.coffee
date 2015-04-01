esprima = require 'esprima'
normalizer = require 'JS_WALA/normalizer/lib/normalizer'
escodegen = require 'escodegen'
_ = require 'lodash'

V =
  mt: [[],[]]
  union: ([f1,o1],[f2,o2]) ->
    [_.union(f1, f2), _.union(o1, o2)]

analysis =

  parse: (src) ->
    esprima.parse src, {loc: true, range: true}

  normalize: (ast) ->
    normalizer.normalize ast,
      reference_errors: true
      unify_ret: true

  codegen: (ast) ->
    {code,map} = escodegen.generate ast,
      sourceMap: 'foo'
      sourceMapWithCode: true
    code

  resolveBranches: (ast) ->
    func = []
    f = (node) -> return unless node; switch node.type
      when 'Program', 'BlockStatement'
        f n for n in node.body
      when 'ExpressionStatement'
        f node.expression
      when 'IfStatement', 'ConditionalExpression'
        f node.test
        f node.consequent
        f node.alternate
      when 'LabeledStatement'
        _.last(func).attr.labels[node.label] = node
        f node.body
      when 'EmptyStatement' then # do nothing
      when 'BreakStatement' then
        if _.last(func).attr.labels?.hasOwnProperty node.label
          node.attr.to = _.last(func).attr.labels[node.label]
      #when "ContinueStatement" then # -- desugared to break
      when 'WithStatement' then throw Error 'with not supported'
      when 'SwitchStatement'
        f node.discriminant
        f caze for caze in node.cases
      when 'SwitchCase'
        f node.test
        f node.consequent
      when 'ReturnStatement'
        f node.argument
      when 'ThrowStatement'
        f node.argument
      when 'TryStatement'
        f node.block
        f node.handler
        f handler for handler in node.guardedHandlers
        f node.finalizer
      when 'CatchClause'
        f node.guard
        f node.body
      when 'WhileStatement'
        f node.test
        f node.body
      #when "DoWhileStatement" then # -- desugared to while
      #when "ForStatement" then # -- desugared to while
      when 'ForInStatement'
        f node.left
        f node.right
        f node.body
      when 'ForOfStatement' then throw Error 'for of not supported'
      when 'LetStatement' then throw Error 'let not supported'
      when 'DebuggerStatement' then throw Error 'debugger not supported'
      when 'FunctionDeclaration', 'FunctionExpression', 'ArrowExpression'
        func.push node
        if node.defaults
          f def for def in node.defaults
        f node.body
        func.pop()
      when 'VariableDeclaration'
        f decl for decl in node.declarations
      when 'VariableDeclarator'
        f node.init
      when 'ThisExpression' then # do nothing
      when 'ArrayExpression'
        if node.elements
          f e for e in node.elements
      when 'ObjectExpression'
        f prop for prop in node.properties
      when 'Property'
        f node.value
      when 'SequenceExpression'
        f expr for expr in node.expressions
      when 'UnaryExpression'
        f node.argument
      when 'BinaryExpression'
        f node.left
        f node.right
      when 'AssignmentExpression'
        f node.left
        f node.right
      when 'UpdateExpression'
        f node.argument
      when 'LogicalExpression'
        f node.left
        f node.right
      when 'CallExpression', 'NewExpression'
        f node.callee
        f arg for arg in node.arguments
      when 'MemberExpression'
        f node.object
        f node.property if node.computed
      when 'YieldExpression' then throw Error 'yield not supported'
      when 'ComprehensionExpression' then throw Error 'compreh. not supported'
      when 'GeneratorExpression' then throw Error 'generators not supported'
      when 'Identifier' then # do nothing
      when 'Literal' then # do nothing
      else
        throw Error 'Unknown AST node'
    f ast
    f ast

  analyze: (src) ->
    ast = @normalize @parse src
    envs = []
    funcs = []
    objs = []
    f = (node) -> return V.mt unless node; switch node.type
      when 'Program', 'BlockStatement'
        f n for n in node.body
        V.mt
      when 'ExpressionStatement'
        f node.expression
        V.mt
      when 'IfStatement', 'ConditionalExpression'
        f node.test
        V.union f node.consequent, f node.alternate
      when 'LabeledStatement'
        f node.body
      when 'EmptyStatement' then # do nothing
      when 'BreakStatement' then # always has label
      #when "ContinueStatement" then # -- desugared to break
      when 'WithStatement' then throw Error 'with not supported'
      when 'SwitchStatement'
        f node.discriminant
        f caze for caze in node.cases
      when 'SwitchCase'
        f node.test
        f node.consequent
      when 'ReturnStatement'
        f node.argument
      when 'ThrowStatement'
        f node.argument
      when 'TryStatement'
        f node.block
        f node.handler
        f handler for handler in node.guardedHandlers
        f node.finalizer
      when 'CatchClause'
        f node.guard
        f node.body
      when 'WhileStatement'
        f node.test
        f node.body
      #when "DoWhileStatement" then # -- desugared to while
      #when "ForStatement" then # -- desugared to while
      when 'ForInStatement'
        f node.left
        f node.right
        f node.body
      when 'ForOfStatement' then throw Error 'for of not supported'
      when 'LetStatement' then throw Error 'let not supported'
      when 'DebuggerStatement' then throw Error 'debugger not supported'
      when 'FunctionDeclaration', 'FunctionExpression', 'ArrowExpression'
        fds.push node.attr.pos
        if node.defaults
          f def for def in node.defaults
        f node.body
      when 'VariableDeclaration'
        f decl for decl in node.declarations
      when 'VariableDeclarator'
        f node.init
      when 'ThisExpression' then # do nothing
      when 'ArrayExpression'
        if node.elements
          f e for e in node.elements
      when 'ObjectExpression'
        f prop for prop in node.properties
      when 'Property'
        f node.value
      when 'SequenceExpression'
        f expr for expr in node.expressions
      when 'UnaryExpression'
        f node.argument
      when 'BinaryExpression'
        f node.left
        f node.right
      when 'AssignmentExpression'
        f node.left
        f node.right
      when 'UpdateExpression'
        f node.argument
      when 'LogicalExpression'
        f node.left
        f node.right
      when 'CallExpression', 'NewExpression'
        f node.callee
        f arg for arg in node.arguments
      when 'MemberExpression'
        f node.object
        f node.property if node.computed
      when 'YieldExpression' then throw Error 'yield not supported'
      when 'ComprehensionExpression' then throw Error 'compreh. not supported'
      when 'GeneratorExpression' then throw Error 'generators not supported'
      when 'Identifier' then # do nothing
      when 'Literal' then # do nothing
      else
        throw Error 'Unknown AST node'
    f ast
    fds

if typeof window != 'undefined'
  window.analysis = analysis
else
  module.exports = analysis
