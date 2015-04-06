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

  it.only 'should work for functions', (done) ->
    validates '(function(i) {})(1)', done
    # validates 'var f = function() { return 23; }', done

  it 'should work for objects', (done) ->
    validates 'a = 1', done

  it 'should use an SMT solver', (done) ->
    a.nodes = ['n1', 'n2', 'n3']
    a.funcs = ['f1']
    a.objs = ['o1']
    a.objConstraints = n2: ['o1']
    a.funcConstraints = n3: ['f1']
    a.flowConstraints =
      n1: ['n2']
      n2: ['n3']
    a.solve (res) ->
      res.should.be.true
      done()

describe 'Normalizer', ->

  a = new Analyzer()

  it 'should hoist variable declarations', ->
    src = 'function f(x) { x = x + 2; return x; }'
    a.parse src
    a.normalize()
    code = a.codegen()
    code.indexOf('var').should.be.below code.indexOf('x')
