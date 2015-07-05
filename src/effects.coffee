_ = require 'lodash'
sweet = require 'sweet.js'
sweet.loadMacro(__dirname + '/../src/fxmacros')

Analyzer = require './analyzer'
CallGraphAnalyzer = require './callgraph'

class EffectConstraint extends Analyzer.Constraint
  constructor: (@infuncidx, @fxid, pos) -> super pos ; @pos = pos
  smt: -> "(effect F#{@infuncidx} FX#{@fxid})"

class ContractConstraint extends Analyzer.Constraint
  constructor: (@node, @fxidx, pos) -> super pos ; @pos = pos
  smt: -> "(contract #{@node} FX#{@fxidx})"

class EffectSystemAnalyzer extends CallGraphAnalyzer

  constructor: -> @effectIdx = 0; @contractIdx = 0; super

  parse: (src) ->
    @ast = sweet.compile src,
      ast: true
      readableNames: true

  run: (src, cb) ->
    @code = src
    @fxs = {}
    super src, cb

  fx: (fx) ->
    unless @fxs.hasOwnProperty fx
      @fxs[fx] = 1 + _.keys(@fxs).length
    @fxs[fx]

  regExPosFor: (re, idx) ->
    notFound =
      start_offset: 0
      end_offset: 0
    while idx >= 0 and (m = re.exec @code) != null
      if idx-- == 0
        a =
          start_offset: re.lastIndex - m[0].length
          end_offset: re.lastIndex
        return a
    notFound

  effectPosFor: (idx) -> @regExPosFor /fx\[[^!\]]+\]/g, idx

  contractPosFor: (idx) -> @regExPosFor /fx\[![^\]]+\]/g, idx

  effect: (funcidx, fx, pos) ->
    pos = @effectPosFor @effectIdx++
    @constraints.push new EffectConstraint funcidx, (@fx fx), [pos]

  contract: (node, fx, pos) ->
    pos = @contractPosFor @contractIdx++
    @constraints.push new ContractConstraint node, (@fx fx), [pos]

  fxRegex: /^__@fx:(.+)$/
  contractRegex: /^__@var:([^:]+):(.+)$/

  visitLiteral: (x, lit, pos) ->
    if typeof lit is 'string' and @fxRegex.test lit
      @effect @funcs, fx, pos for fx in lit.match(@fxRegex)[1].split ','
    else if typeof lit is 'string' and @contractRegex.test lit
      [all, varname, fxs] = lit.match @contractRegex
      @contract (@var varname), fx.substr(1), pos for fx in fxs.split ','
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
