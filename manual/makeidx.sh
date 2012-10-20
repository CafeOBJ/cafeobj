# make index and glossary for manual
echo Making the indexes and glossary for manual
makeindex -s manual.ist manual.idx
makeindex lines.idx
# makeindex -s manual.gst -o manual.gls manual.glo
echo
