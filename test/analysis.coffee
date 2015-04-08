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

  shouldFail = (done,f) ->
    a = new EffectSystemAnalyzer()
    a.run "(#{f})()", (res) ->
      res.should.be.false
      done()

  shouldSucceed = (done,f) ->
    a = new EffectSystemAnalyzer()
    a.run "(#{f})()", (res) ->
      res.should.be.true
      done()

  it 'should work without contracts', (done) ->
    shouldSucceed done, ->
      a = -> '__@fx:io'
      b = -> b()
      c = (x) -> '__@var:x:!io'
      c b

  it 'should fail with a direct call', (done) ->
    shouldFail done, ->
      a = -> '__@fx:io'
      b = (x) -> '__@var:x:!io'
      b a

  it 'should fail with an indirect call', (done) ->
    shouldFail done, ->
      a = -> '__@fx:io'
      b = -> a()
      c = (x) -> '__@var:x:!io'
      c b

  it 'should work with objects', (done) ->
    shouldFail done, ->
      o = f: -> '__@fx:io'
      b = -> o.f()
      c = (x) -> '__@var:x:!io'
      c b

  it 'should work with closures', (done) ->
    shouldFail done, ->
      box = ->
        -> '__@fx:io'
      b = box()
      c = (x) -> '__@var:x:!io'
      c b

  it 'should fail with object updates', (done) ->
    shouldFail done, ->
      o = {}
      a = -> '__@fx:dom'
      b = -> o.f()
      c = (x) -> '__@var:x:!dom'
      c b
      o.f = a

  it 'should work with object aliases', (done) ->
    shouldSucceed done, ->
      alert = -> '__@fx:dom'
      startWorker = (x) -> '__@var:x:!dom'
      obj = f: (i) -> i
      box = (x) ->
        -> x
      b = box obj
      startWorker -> b().f()

  it 'should fail with object aliases', (done) ->
    shouldFail done, ->
      alert = -> '__@fx:dom'
      startWorker = (x) -> '__@var:x:!dom'
      obj = f: (i) -> i
      box = (x) ->
        -> x
      b = box obj
      startWorker -> b().f()
      obj.f = alert

  it 'should work with object receiver', (done) ->
    shouldSucceed done, ->
      alert = -> '__@fx:dom'
      startWorker = (x) -> '__@var:x:!dom'
      obj =
        f: alert
        g: -> @g()
      startWorker -> obj.g()

  it 'should fail with object receiver', (done) ->
    shouldFail done, ->
      alert = -> '__@fx:dom'
      startWorker = (x) -> '__@var:x:!dom'
      obj =
        f: alert
        g: -> @f()
      startWorker -> obj.g()

  it 'should work with computed object property get', (done) ->
    shouldSucceed done, ->
      alert = -> '__@fx:dom'
      startWorker = (x) -> '__@var:x:!dom'
      obj =
        p: 'f'
        g: -> this[@p]()
      startWorker -> obj.g()

  it 'should fail with computed object property get', (done) ->
    shouldFail done, ->
      alert = -> '__@fx:dom'
      startWorker = (x) -> '__@var:x:!dom'
      obj =
        p: 'f'
        f: alert
        g: -> this[@p]()
      startWorker -> obj.g()

  it 'should work with computed object property set', (done) ->
    shouldSucceed done, ->
      alert = -> '__@fx:dom'
      startWorker = (x) -> '__@var:x:!dom'
      obj =
        g: -> 23
      p = 'g'
      obj[p] = -> 'foo'
      startWorker -> obj.g()

  it 'should fail with computed object property set', (done) ->
    shouldFail done, ->
      alert = -> '__@fx:dom'
      startWorker = (x) -> '__@var:x:!dom'
      obj =
        g: -> 23
      p = 'g'
      obj[p] = alert
      startWorker -> obj.g()

