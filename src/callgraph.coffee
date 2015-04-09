_ = require 'lodash'

Analyzer = require './analyzer'

class FunctionCallConstraint extends Analyzer.Constraint
  constructor: (@infuncidx, @func, pos) -> super pos
  smt: -> "(call F#{@infuncidx} #{@func})"

class MethodCallConstraint extends Analyzer.Constraint
  constructor: (@infuncidx, @obj, @propidx, pos) -> super pos
  smt: -> "(mcall F#{@infuncidx} #{@obj} S#{@propidx})"

class CallGraphAnalyzer extends Analyzer
  call: (funcidx, to, pos) ->
    @constraints.push new FunctionCallConstraint funcidx, to, pos

  mcall: (funcidx, obj, prop, pos) ->
    @constraints.push new MethodCallConstraint funcidx, obj,  (@prop prop), pos
  # Id, Id, [Id]
  visitCall: (x, f, args, pos) ->
    super x, f, args, pos
    @call _.last(@scopes)['#f'], (@var f), [pos[1]]

  # Id, Id, Id, [Id]
  visitMethodCall: (x, o, f, args, pos) ->
    super x, o, f, args, pos
    @mcall _.last(@scopes)['#f'], (@var o), (@var f), [pos[1],pos[2]]

  # Id, Id, [Id]
  visitConstructorCall: (x, f, args, pos) ->
    super x, f, args, pos
    @call _.last(@scopes)['#f'], (@var f), [pos[1]]

if typeof window != 'undefined'
  window.CallGraphAnalyzer = CallGraphAnalyzer
else
  module.exports = CallGraphAnalyzer
