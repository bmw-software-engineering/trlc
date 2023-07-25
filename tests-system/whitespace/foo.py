with open("test.trlc", "r") as fd:
    txt = fd.read()

txt += "\n\npackage"

txt += b' \t\n\r\x0b\f'.decode("UTF-8")

txt += "Potato"

with open("test.trlc", "w") as fd:
    fd.write(txt)
