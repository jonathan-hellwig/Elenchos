command = `java -jar jar/keymaerax.jar -prove kyx/test.kyx -launch`
output = read(command, String)
lines = split(output, "\n")
process = run(`ls`)