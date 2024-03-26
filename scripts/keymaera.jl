# command = `java -jar jar/keymaerax.jar -prove kyx/test.kyx -launch`
# output = read(command, String)
# lines = split(output, "\n")
# process = run(`ls`)
using HTTP
f = open("kyx/test.kyx", "r")
kyx_string = read(f, String)
println(kyx_string)
response = nothing
is_success = true
response = HTTP.post("http://localhost:8070/check", Dict("Content-Type" => "text/plain"), kyx_string)
# try
#     response = HTTP.post("http://localhost:8070/check", Dict("Content-Type" => "text/plain"), kyx_string)
# catch
#     println("Failed to send proof request")
#     is_success = false
# end
# is_success = parse_response(response)
# if isnothing(is_success)
#     println("Unexpected error")
#     return
# end
# if is_success
#     println("Proved")
# else
#     println("Failed to prove")
# end