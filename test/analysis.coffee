chai = require 'chai'
analysis = require '../src/analysis'
_ = require 'lodash'

chai.should()
expect = chai.expect

describe 'funcdefs', ->

  it 'should list function definitions', ->
    src = 'var f = function() { return 23; }'
    res = analysis.funcdefs src
    res.should.be.an 'array'
    res.length.should.eql 2
    _.assign({},res[1]).should.eql
      url: '<unknown>'
      start_line: 1
      start_offset: 8
      end_line: 1
      end_offset: 33

  it 'should list inner function definitions', ->
    src = 'var f = function() { return function() { }; }'
    res = analysis.funcdefs src
    res.length.should.eql 3
