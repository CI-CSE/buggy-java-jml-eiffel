note
	model: reverse

class
	STR_PALINDROME

create
	make

feature
	reverse: STR_P_STRING

	make
		do
			create reverse.make_empty
		ensure
			reverse.count = 0
		end

	is_palindrome (str: STR_P_STRING): BOOLEAN
		note
			status: impure
			explicit: wrapping
		require
			reverse.is_wrapped
		local
			length: INTEGER
			i_counter: INTEGER
			i: INTEGER
		do
			length := str.count

			from
				i := length
				i_counter := 0
			invariant
				is_wrapped
				length = str.count
				reverse.is_wrapped

				i_bounds: 0 <= i and i <= str.count
				i_counter_def: i_counter + i = length
			until
				0 >= i
			loop
				unwrap
				reverse := reverse.char_extended (str [i])
				wrap

				i_counter := i_counter + 1
				i := i - 1
			end

			check i_counter_full: i_counter = length end

			Result := reverse.sequence = str.sequence
		ensure
			modify_model ("reverse", Current)

			res_def: Result = (reverse.sequence = str.sequence)
		end

end
