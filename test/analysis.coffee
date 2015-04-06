chai = require 'chai'
Analyzer = require '../src/analyzer'
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
    validates 'a = 1', done

describe 'Normalizer', ->

  a = new Analyzer()

  it 'should hoist variable declarations', ->
    src = 'function f(x) { x = x + 2; return x; }'
    a.parse src
    a.normalize()
    code = a.codegen()
    code.indexOf('var').should.be.below code.indexOf('x')
