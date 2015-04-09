express = require 'express'
logger = require 'morgan'
bodyParser = require 'body-parser'
EffectSystemAnalyzer = require './effects'

app = express()
app.use logger ':remote-addr :method :url
                :status :res[content-length] :response-time ms'
app.use bodyParser.urlencoded extended: true
app.use bodyParser.json()
app.use express.static(__dirname + '/../dist')

app.get '/', (req, res, next) ->
  req.url = '/index.html'
  next()

app.post '/compile', (req, res) ->
  a = new EffectSystemAnalyzer()
  try
    a.run req.body.code, (result) ->
      res.send result
  catch
    res.send parseError: true

server = app.listen 3000, ->
  host = server.address().address
  port = server.address().port
  console.log 'JSFX listening at http://%s:%s', host, port
