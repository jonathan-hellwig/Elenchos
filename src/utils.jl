function snake_case_to_camel_case(s::AbstractString)
    words = split(s, '_')
    result = words[1] * join(uppercasefirst.(words[2:end]))
    return result
end

export snake_case_to_camel_case