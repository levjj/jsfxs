diskOutdated = false
renderOutdated = true

textarea = undefined
outputarea = undefined
filePicker = undefined

window.addEventListener('beforeunload', (e) ->
  if diskOutdated
    e.returnValue = 'Are you sure you want to leave this page?'
)

window.App =
  init: ->
    textarea = CodeMirror $('#source .panel-body').get(0),
      value: code
      mode: 'javascript'
      indentUnit: 4

    outputarea = $('#output')

    $('#loadButton').click(load)
    filePicker = $('#filePicker')
    filePicker.on('change', load2)

    $('#saveButton').click(save)

    setInterval(possiblyUpdate, 2000)

    $('#vimmode').on 'change', ->
      console.log $('#vimmode').is(':checked')
      textarea.setOption 'vimMode', $('#vimmode').is(':checked')

possiblyUpdate = ->
  if code != textarea.getValue()
    diskOutdated = true
    renderOutdated = true
  code = textarea.getValue()

  return if !renderOutdated

  renderOutdated = false

  funcdefs = analysis
  outputarea.html "<pre>#{JSON.stringify funcdefs}</pre>"

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
