_ = require 'lodash'

Analyzer = require './analyzer'

class Constraint

class FunctionCallConstraint extends Constraint
  constructor: (@infuncidx, @func) ->
  toString: -> "(call F#{@infuncidx} #{@func})"

class MethodCallConstraint extends Constraint
  constructor: (@infuncidx, @obj, @propidx) ->
  toString: -> "(mcall F#{@infuncidx} #{@obj} S#{@propidx})"

class CallGraphAnalyzer extends Analyzer
  call: (funcidx, to) ->
    @constraints.push new FunctionCallConstraint funcidx, to

  mcall: (funcidx, obj, prop) ->
    @constraints.push new MethodCallConstraint funcidx, obj,  (@prop prop)

  # Id, Id, [Id]
  visitCall: (x, f, args) ->
    super x, f, args
    @call _.last(@scopes)['#f'], (@var f)

  # Id, Id, Id, [Id]
  visitMethodCall: (x, o, f, args) ->
    super x, o, f, args
    @mcall _.last(@scopes)['#f'], (@var o), (@var f)

  # Id, Id, [Id]
  visitConstructorCall: (x, f, args) ->
    super x, f, args
    @call _.last(@scopes)['#f'], (@var f)

if typeof window != 'undefined'
  window.CallGraphAnalyzer = CallGraphAnalyzer
else
  module.exports = CallGraphAnalyzer
