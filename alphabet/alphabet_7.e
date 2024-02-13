note
	model: vowel, vowel_set, alphabetic, alphabetic_set, digit, digit_set, uppercase, uppercase_set, lowercase, lowercase_set

class
	ALPHABET_7

create
	make

feature {NONE} -- Constructors
	make (a_c: CHARACTER)
		note
			status: creator
		do
			c := a_c
		ensure
				-- Private
			not_vowel: not vowel_set
			not_alphabtic: not alphabetic_set
			not_digit: not digit_set
			not_uppercase: not uppercase_set
			not_lowercase: not lowercase_set
				-- Public
			c_set: c = a_c
		end

feature
	vowel_set: BOOLEAN
	vowel: BOOLEAN
	alphabetic_set: BOOLEAN
	alphabetic: BOOLEAN
	digit_set: BOOLEAN
	digit: BOOLEAN
	uppercase_set: BOOLEAN
	uppercase: BOOLEAN
	lowercase_set: BOOLEAN
	lowercase: BOOLEAN

	c: CHARACTER

feature
	is_vowel: BOOLEAN
		note
			status: impure
		do
			set_vowel
			Result := vowel
		ensure
				-- Private
			modifies_clause: modify_model (["vowel_set", "vowel"], Current)
			fields_effect: vowel_set and (Result = vowel)
				-- Public
			result_iff_vowel: Result = (c = 'a' or c = 'A' or c = 'e' or c = 'E' or c = 'i' or c = 'I' or c = 'o' or c = 'O' or c = 'u' or c = 'U')
		end

	is_alphabetic: BOOLEAN
		note
			status: impure
		do
			set_alphabetic
			Result := alphabetic
		ensure
				-- Private
			modifies_clause: modify_model (["alphabetic_set", "alphabetic"], Current)
			fields_effect: alphabetic_set and (Result = alphabetic)
				-- Public
			result_iff_alphabetic: Result = ('a' <= c and c <= 'z') or ('A' <= c and c <= 'Z')
		end

	is_uppercase: BOOLEAN
		note
			status: impure
		do
			set_uppercase
			Result := uppercase
		ensure
				-- Private
			modifies_clause: modify_model (["uppercase_set", "uppercase"], Current)
			fields_effect: uppercase_set and (Result = uppercase)
				-- Public
			result_iff_uppercase: Result = ('A' <= c and c <= 'Z')
		end

	is_lowercase: BOOLEAN
		note
			status: impure
		do
			Result := lowercase
		ensure
				-- Private
			modifies_clause: modify_model (["lowercase_set", "lowercase"], Current)
			fields_effect: lowercase_set and (Result = lowercase)
				-- Public
			result_iff_lowercase: Result = ('a' <= c and c <= 'z')
		end

	is_digit: BOOLEAN
		note
			status: impure
		do
			set_digit
			Result := digit
		ensure
				-- Private
			modifies_clause: modify_model (["digit_set", "digit"], Current)
			fields_effect: digit_set and (Result = digit)
				-- Public
			result_iff_digit: Result = ('0' <= c and c <= '9')
		end

	set_vowel
		do
			vowel := False
			inspect c
			when 'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U' then
				vowel := True
			else
			end
			vowel_set := True
		ensure
			modifies_clause: modify_model (["vowel_set", "vowel"], Current)
			fields_effect: vowel_set
			vowel_iff_c_vowel: vowel = (c = 'a' or c = 'A' or c = 'e' or c = 'E' or c = 'i' or c = 'I' or c = 'o' or c = 'O' or c = 'u' or c = 'U')
		end

	set_alphabetic
		do
			alphabetic := (('a' <= c and c <= 'z') or ('A' <= c and c <= 'Z'))
			alphabetic_set := True
		ensure
			modifies_clause: modify_model (["alphabetic_set", "alphabetic"], Current)
			fields_effect: alphabetic_set
			alphabetic_iff_c_alphabetic: alphabetic = (('a' <= c and c <= 'z') or ('A' <= c and c <= 'Z'))
		end

	set_uppercase
		do
			uppercase := ('A' <= c and c <= 'Z')
			uppercase_set := True
		ensure
			modifies_clause: modify_model (["uppercase_set", "uppercase"], Current)
			fields_effect: uppercase_set
			uppercase_iff_c_uppercase: uppercase = ('A' <= c and c <= 'Z')
		end

	set_lowercase
		do
			lowercase := ('a' <= c and c <= 'z')
			lowercase_set := True
		ensure
			modifies_clause: modify_model (["lowercase_set", "lowercase"], Current)
			fields_effect: lowercase_set
			lowercase_iff_c_lowercase: lowercase = ('a' <= c and c <= 'z')
		end

	set_digit
		do
			digit := ('0' <= c and c <= '9')
			digit_set := True
		ensure
			modifies_clause: modify_model (["digit_set", "digit"], Current)
			fields_effect: digit_set
			digit_iff_c_digit: digit = ('0' <= c and c <= '9')
		end

	get_alphabetic_set: BOOLEAN
		do
			Result := alphabetic_set
		ensure
			result_is_alphabetic_set: Result = alphabetic_set
		end

	get_uppercase_set: BOOLEAN
		do
			Result := uppercase_set
		ensure
			result_is_uppercase_set: Result = uppercase_set
		end

	get_lowercase_set: BOOLEAN
		do
			Result := lowercase_set
		ensure
			result_is_lowercase_set: Result = lowercase_set
		end

	get_vowel_set: BOOLEAN
		do
			Result := vowel_set
		ensure
			result_is_vowel_set: Result = vowel_set
		end

	get_digit_set: BOOLEAN
		do
			Result := digit_set
		ensure
			result_is_digit_set: Result = digit_set
		end

	driver (op: INTEGER): SIMPLE_ARRAY [BOOLEAN]
		note
			status: impure
		require
			op_is_0_1_2_3_4: 0 <= op and op <= 4
		do
			create Result.make (6)
			inspect op
			when 0 then
				Result [1] := is_vowel
				Result [2] := get_vowel_set
			when 1 then
				Result [1] := is_uppercase
				Result [3] := get_uppercase_set
			when 2 then
				Result [1] := is_lowercase
				Result [4] := get_lowercase_set
			when 3 then
				Result [1] := is_digit
				Result [5] := get_digit_set
			else
				Result [1] := is_alphabetic
				Result [6] := get_alphabetic_set
			end
				-- return result;
		ensure
			modifiest_clause: modify (Current)
			operation_0: op = 0 implies (Result [2] and
					(Result [1] implies (c = 'a' or c = 'A' or c = 'e' or c = 'E' or c = 'i' or c = 'I' or c = 'o' or c = 'O' or c = 'u' or c = 'U')))
			operation_1: op = 1 implies (Result [3] and (Result [1] implies ('A' <= c and c <= 'Z')))
			operation_2: op = 2 implies (Result [4] and (Result [1] implies ('a' <= c and c <= 'z')))
			operation_3: op = 3 implies (Result [5] and (Result [1] implies ('0' <= c and c <= '9')))
			operation_4: op = 4 implies Result [6]
		end

invariant
	vowel_set_inv: vowel_set implies (vowel = (c = 'a' or c = 'A' or c = 'e' or c = 'E' or c = 'i' or c = 'I' or c = 'o' or c = 'O' or c = 'u' or c = 'U'))
	alphabetic_set_inv: alphabetic_set implies (alphabetic = (('a' <= c and c <= 'z') or ('A' <= c and c <= 'Z')))
	digit_set_inv: digit_set implies (digit = ('0' <= c and c <= '9'))
	uppercase_set_inv: uppercase_set implies (uppercase = ('A' <= c and c <= 'Z'))
	lowercase_set_inv: lowercase_set implies (lowercase = ('a' <= c and c <= 'z'))

end
