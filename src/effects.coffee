_ = require 'lodash'

CallGraphAnalyzer = require './callgraph'

class Constraint

class EffectConstraint extends Constraint
  constructor: (@infuncidx, @fxid) ->
  toString: -> "(effect F#{@infuncidx} FX#{@fxid})"

class ContractConstraint extends Constraint
  constructor: (@infuncidx, @argidx, @fxidx) ->
  toString: -> "(contract F#{@infuncidx} A#{@argidx} FX#{@fxidx})"

class EffectSystemAnalyzer extends CallGraphAnalyzer
  run: (src,cb) ->
    @fxs = {}
    super src, cb

  fx: (fx) ->
    unless @fxs.hasOwnProperty fx
      @fxs[fx] = 1 + _.keys(@fxs).length
    @fxs[fx]

  effect: (funcidx, fx) ->
    @constraints.push new EffectConstraint funcidx, (@fx fx)

  contract: (funcidx, argidx, fx) ->
    @constraints.push new ContractConstraint funcidx, argidx, (@fx fx)

  fxRegex: /^__@fx:(.+)$/
  contractRegex: /^__@arg:([0-9]+):(.+)$/

  visitLiteral: (x, lit) ->
    if typeof lit is 'string' and @fxRegex.test lit
      @effect @funcs, lit.match(@fxRegex)[1]
    else if typeof lit is 'string' and @contractRegex.test lit
      [all, argidx, fx] = lit.match @contractRegex
      @contract @funcs, +argidx, fx
    else
      super x, lit

  templateData: ->
    data = super()
    data.fxs = _.keys(@fxs).length || 1
    data

if typeof window != 'undefined'
  window.EffectSystemAnalyzer = EffectSystemAnalyzer
else
  module.exports = EffectSystemAnalyzer
