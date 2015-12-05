diskOutdated = false
renderOutdated = true

textarea = undefined
outputarea = undefined
filePicker = undefined

window.addEventListener 'beforeunload', (e) ->
  if diskOutdated
    e.returnValue = 'Are you sure you want to leave this page?'

code = '''
       var alert = function() fx[dom] {
           // alert has an effect on the dom
       }
       var startWorker = function(func fx[!dom]) {
           // startWorker expects a function without dom effects
       }
       var obj = {f: function() { } };
       var box = function (x) {
           return function() { return x; }
       };
       var b = box(obj);
       startWorker(function() {
           b().f();
       });
       obj.f = alert;  // this assignment might cause a crash
       '''

window.App =
  init: ->
    CodeMirror.extendMode 'javascript', token: (stream, state) ->
      if stream.match 'fx', false
        @_token stream, state
        'keyword'
      else
        @_token stream, state
    textarea = CodeMirror $('#source .panel-body').get(0),
      value: code
      mode: 'javascript'
      indentUnit: 4

    $('#loadButton').click load
    filePicker = $('#filePicker')
    filePicker.on('change', load2)

    $('#saveButton').click save
    $('#checkButton').click startUpdate
    textarea.on 'change', startUpdate

    $('#vimmode').on 'change', ->
      console.log $('#vimmode').is(':checked')
      textarea.setOption 'vimMode', $('#vimmode').is(':checked')

startUpdate = ->
  $('#source .panel').removeClass 'panel-default'
  $('#source .panel').removeClass 'panel-danger'
  $('#source .panel').removeClass 'panel-success'
  $('#source .panel').addClass 'panel-warning'
  $('#msg').html 'Checking...'
  possiblyUpdate()

update = ->
  code = textarea.getValue()
  $('#source .panel').removeClass 'panel-warning'
  analyze()

possiblyUpdate = _.debounce update, 2000

analyze = ->
  $.post 'compile', code: code, (data) ->
    if data.parseError
      $('#msg').html 'Parse error!'
      $('#source .panel').addClass 'panel-danger'
      highlight []
    else if data.success
      $('#msg').html 'Effect checking complete. No errors found.'
      $('#source .panel').addClass 'panel-success'
      highlight []
    else
      fxerr = code.substring data.pos[0][0], data.pos[0][1]
      fx = fxerr.match(/fx\[!?([^\]]+)\]/)[1]
      $('#msg').html "Error: '#{fx}' effect not allowed here."
      $('#source .panel').addClass 'panel-danger'
      highlight data.pos

load = ->
  if diskOutdated
    if !window.confirm('Are you sure you want to load a new file without' +
                       'saving this one first?')
      return
  filePicker[0].click()

load2 = ->
  file = filePicker[0].files[0]
  if file == undefined
    console.log('file is undefined')
    return
  reader = new FileReader()
  reader.onload = (_) ->
    if reader.result == undefined
      console.log('file contents are undefined')
      return

    # Populate the text field with the new source code
    code = reader.result
    textarea.setValue(reader.result)
    diskOutdated = false
    renderOutdated = true

  reader.readAsText(file)

save = ->
  console.log('attempting to save')
  download('file.ctm', textarea.getValue())

download = (filename, text) ->
  a = $('<a>')
  a.attr
    href: 'data:text/plain;charset=utf-8,' + encodeURIComponent(text)
    download: filename
  a.appendTo($('body'))
  a[0].click()
  a.remove()
  diskOutdated = false

convPos = (pos) ->
  offset = 0
  for s,i in code.split /\n/
    if offset + s.length >= pos
      return { line: i + 1, column: pos - offset }
    offset += s.length + 1
  line: 0
  column: 0

convRange = (range) ->
  start: convPos range[0]
  end: convPos range[1]

highlight = (highlights) ->
  textarea.removeOverlay 'violation'
  highlights = highlights.map convRange
  highlights.sort (a, b) ->
    return -1 if a.start.line < b.start.line
    return 1 if a.start.line > b.start.line
    a.start.column - b.start.column
  line = 0
  currentIdx = 0
  textarea.addOverlay
    name: 'violation'
    token: (stream) ->
      line++ if stream.sol()
      if currentIdx >= highlights.length # no more highlights
        stream.skipToEnd()
        return null

      current = highlights[currentIdx]
      if current.start.line > line # no highlights on this line
        stream.skipToEnd()
        return null

      if current.start.column > stream.pos # skip to highlight
        stream.pos = current.start.column
        return null

      if current.start.column < stream.pos # omit past highlight
        currentIdx++
        return null

      # highlight current token
      if current.end.line == line && stream.pos < current.end.column
        stream.pos = current.end.column
        currentIdx++
      else if current.end.line <= line # omit empty highlight
        currentIdx++
      else # multi-line token -> move to next line
        current.start.column = 0
        stream.skipToEnd()
      'violation'

    blankLine: -> line++ ; null
