chai = require 'chai'
Analyzer = require '../src/analyzer'
CallGraphAnalyzer = require '../src/callgraph'
EffectSystemAnalyzer =  require '../src/effects'
_ = require 'lodash'

chai.should()
expect = chai.expect

describe 'Analyzer', ->

  validates = (src, done) ->
    a = new Analyzer()
    a.run src, (res) ->
      res.should.be.true
      done()

  it 'should work for functions', (done) ->
    validates '(function() {})()', ->
      validates '(function(i) {return i;})(23)', done

  it 'should work for omega', (done) ->
    f = ->
      a = -> b()
      b = -> a()
      a()
    validates "(#{f})()", done

  it 'should work for objects', (done) ->
    f = ->
      a = c: 1
      b = a
      b.c = a
    validates "(#{f})()", done

  it 'should respect receivers', (done) ->
    f = ->
      o = {}
      Box = (@s) ->
      b = new Box o
      b.s
    validates "(#{f})()", done

describe 'Normalizer', ->

  a = new Analyzer()

  it 'should hoist variable declarations', ->
    src = 'function f(x) { x = x + 2; return x; }'
    a.parse src
    a.normalize()
    code = a.codegen()
    code.indexOf('var').should.be.below code.indexOf('x')

describe 'CallGraphAnalyzer', ->

  it 'should work for functions', (done) ->
    f = ->
      a = -> b()
      b = -> c()
    a = new CallGraphAnalyzer()
    a.run "(#{f})()", (res) ->
      res.should.be.true
      done()

describe 'EffectSystemAnalyzer', ->

  it 'should work without contracts', (done) ->
    f = ->
      a = -> '__@fx:io'
      b = -> b()
      c = (x) -> '__@arg:1:io'
      c b
    a = new EffectSystemAnalyzer()
    a.run "(#{f})()", (res) ->
      res.should.be.true
      done()

  it 'should fail with a direct call', (done) ->
    f = ->
      a = -> '__@fx:io'
      b = (x) -> '__@arg:1:io'
      b a
    a = new EffectSystemAnalyzer()
    a.run "(#{f})()", (res) ->
      res.should.be.false
      done()

  it 'should fail with an indirect call', (done) ->
    f = ->
      a = -> '__@fx:io'
      b = -> a()
      c = (x) -> '__@arg:1:io'
      c b
    a = new EffectSystemAnalyzer()
    a.run "(#{f})()", (res) ->
      res.should.be.false
      done()

  it 'should work with objects', (done) ->
    f = ->
      o = f: -> '__@fx:io'
      b = -> o.f()
      c = (x) -> '__@arg:1:io'
      c b
    a = new EffectSystemAnalyzer()
    a.run "(#{f})()", (res) ->
      res.should.be.false
      done()

  it 'should work with closures', (done) ->
    f = ->
      box = ->
        -> '__@fx:io'
      b = box()
      c = (x) -> '__@arg:1:io'
      c b
    a = new EffectSystemAnalyzer()
    a.run "(#{f})()", (res) ->
      res.should.be.false
      done()

  it 'should fail with object updates', (done) ->
    f = ->
      o = {}
      a = -> '__@fx:dom'
      b = -> o.f()
      c = (x) -> '__@arg:1:dom'
      c b
      o.f = a
    a = new EffectSystemAnalyzer()
    a.run "(#{f})()", (res) ->
      res.should.be.false
      done()

  it 'should work with object aliases', (done) ->
    f = ->
      alert = -> '__@fx:dom'
      startWorker = (x) -> '__@arg:1:dom'
      obj = f: (i) -> i
      box = (x) ->
        -> x
      b = box obj
      startWorker -> b().f()
    a = new EffectSystemAnalyzer()
    a.run "(#{f})()", (res) ->
      res.should.be.true
      done()

  it 'should fail with object aliases', (done) ->
    f = ->
      alert = -> '__@fx:dom'
      startWorker = (x) -> '__@arg:1:dom'
      obj = f: (i) -> i
      box = (x) ->
        -> x
      b = box obj
      startWorker -> b().f()
      obj.f = alert
    a = new EffectSystemAnalyzer()
    a.run "(#{f})()", (res) ->
      res.should.be.false
      done()
