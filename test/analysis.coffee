chai = require 'chai'
Analyzer = require '../src/analyzer'
_ = require 'lodash'

chai.should()
expect = chai.expect

describe 'Analyzer', ->

  a = new Analyzer()

  afterEach -> a = new Analyzer()

  it 'should work fine for tiny examples', (done) ->
    src = 'var f = function() { return 23; }'
    a.validate src, (res) ->
      res.should.be.true
      done()

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
    src = 'function f(a) { a = x + 2; var x; return a; }'
    a.parse src
    a.normalize()
    code = a.codegen()
    code.indexOf('var').should.be.below code.indexOf('x')
