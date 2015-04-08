_ = require 'lodash'
sweet = require 'sweet.js'
sweet.loadMacro(__dirname + '/../src/fxmacros')

CallGraphAnalyzer = require './callgraph'

class Constraint

class EffectConstraint extends Constraint
  constructor: (@infuncidx, @fxid) ->
  toString: -> "(effect F#{@infuncidx} FX#{@fxid})"

class ContractConstraint extends Constraint
  constructor: (@node, @fxidx) ->
  toString: -> "(contract #{@node} FX#{@fxidx})"

class EffectSystemAnalyzer extends CallGraphAnalyzer

  parse: (src) ->
    @ast = sweet.compile "#{@macro}\n#{src}",
      ast: true
      readableNames: true

  run: (src,cb) ->
    @fxs = {}
    super src, cb

  fx: (fx) ->
    unless @fxs.hasOwnProperty fx
      @fxs[fx] = 1 + _.keys(@fxs).length
    @fxs[fx]

  effect: (funcidx, fx) ->
    @constraints.push new EffectConstraint funcidx, (@fx fx)

  contract: (node, fx) ->
    @constraints.push new ContractConstraint node, (@fx fx)

  fxRegex: /^__@fx:(.+)$/
  contractRegex: /^__@var:([^:]+):(.+)$/

  visitLiteral: (x, lit) ->
    if typeof lit is 'string' and @fxRegex.test lit
      @effect @funcs, fx for fx in lit.match(@fxRegex)[1].split ','
    else if typeof lit is 'string' and @contractRegex.test lit
      [all, varname, fxs] = lit.match @contractRegex
      @contract (@var varname), fx.substr(1) for fx in fxs.split ','
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
