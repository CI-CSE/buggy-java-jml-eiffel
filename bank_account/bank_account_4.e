note
	model: balance, previous_transaction

class
	BANK_ACCOUNT_4

create
	make, make_with_balance, make_with_balance_and_previous_transaction

feature {NONE}
	make
			-- Originally BankAccount()
		note
			status: creator
		do
			balance := 0
			previous_transaction := 0
		ensure
			balance_0: balance = 0
			prev_transaction_0: previous_transaction = 0
		end

	make_with_balance (current_balance: INTEGER)
			-- Originally BankAccount(int)
		note
			status: creator
		do
			if current_balance <= 0 then
				balance := 0
			else
				balance := current_balance
			end
			previous_transaction := 0
		ensure
			balance_0_when_curr_non_positive: current_balance <= 0 implies balance = 0
			balance_curr_when_curr_positive: 0 < current_balance implies balance = current_balance
			prev_transaction_0: previous_transaction = 0
		end

	make_with_balance_and_previous_transaction (current_balance, a_previous_transaction: INTEGER)
			-- Originally BankAccount(int, int)
		note
			status: creator
		do
			if current_balance <= 0 then
				balance := 0
			else
				balance := current_balance
			end
			previous_transaction := a_previous_transaction
		ensure
			balance_0_when_curr_non_positive: current_balance <= 0 implies balance = 0
			balance_curr_when_curr_positive: 0 < current_balance implies balance = current_balance
			prev_transaction_set: previous_transaction = a_previous_transaction
		end

feature
	balance: INTEGER
	previous_transaction: INTEGER

	get_balance: INTEGER
		do
			Result := balance
		ensure
			result_is_balance: Result = balance
		end

	get_previous_transaction: INTEGER
		do
			Result := if previous_transaction = 0 then 1 else 0 end -- Result := previous_transaction
		ensure
			result_is_previous_transaction: Result = previous_transaction
		end

	is_valid_amount (a_amount: INTEGER): BOOLEAN
			-- Originally isValid(int)
		note
			status: pure
			explicit: contracts
		do
			if 0 < a_amount then
				Result := True
			else
				Result := False
			end
		ensure
			pos_balance_valid: 0 < a_amount implies Result
			non_pos_balance_invalid: a_amount <= 0 implies not Result
		end

	is_valid_balance_amount (a_balance, a_amount: INTEGER): BOOLEAN
			-- Originally isValid(int, int)
		note
			status: pure
			explicit: contracts
		require
			is_valid_amount (a_amount)
			0 <= a_balance
		do
			if 0 <= a_balance - a_amount then
				Result := True
			else
				Result := False
			end
		ensure
			pos_balance_amount_valid: 0 <= a_balance - a_amount implies Result
			non_pos_balance_amount_invalid: a_balance - a_amount < 0 implies not Result
		end

	deposit (amount: INTEGER)
		do
			if is_valid_amount (amount) then
				balance := balance + amount
				previous_transaction := amount
			end
		ensure
			valid_changes: is_valid_amount (amount) implies (balance = old balance + amount and previous_transaction = amount)
			invalid_stays: not is_valid_amount (amount) implies (balance = old balance and previous_transaction = old previous_transaction)

			modifies_clause: modify_model (["balance", "previous_transaction"], Current)
		end

	withdraw (amount: INTEGER)
		do
			if is_valid_amount (amount) then
				if is_valid_balance_amount (balance, amount) then
					balance := balance - amount
					previous_transaction := - amount
				end
			end
		ensure
			valid2_changes: is_valid_amount (amount) and then is_valid_balance_amount (old balance, amount) implies (balance = old balance - amount and previous_transaction = - amount)
			valid1_stays: is_valid_amount (amount) and then not is_valid_balance_amount (old balance, amount) implies (balance = old balance and previous_transaction = old previous_transaction)
			invalid_stays: not is_valid_amount (amount) implies (balance = old balance and previous_transaction = old previous_transaction)

			modifies_clause: modify_model (["balance", "previous_transaction"], Current)
		end

	check_withdrawal (amount: INTEGER)
		local
			not_enough_money_penalty: INTEGER
			l_balance: INTEGER
		do
			if is_valid_amount (amount) then
				if is_valid_balance_amount (balance, amount) then
					balance := balance - amount
					previous_transaction := - amount
				else
					not_enough_money_penalty := 50
					l_balance := balance - not_enough_money_penalty
					if 0 <= l_balance then
						balance := l_balance
						previous_transaction := - not_enough_money_penalty
					else
						previous_transaction := - balance
						balance := 0
					end
				end
			end
		ensure
			valid2_changes: is_valid_amount (amount) and then is_valid_balance_amount (old balance, amount) implies (balance = old balance - amount and previous_transaction = - amount)
			valid50_changes: is_valid_amount (amount) and then not is_valid_balance_amount (old balance, amount) and then is_valid_balance_amount (old balance, 50) implies (balance = old balance - 50 and previous_transaction = -50)
			invalid50_stays: is_valid_amount (amount) and then not is_valid_balance_amount (old balance, amount) and then not is_valid_balance_amount (old balance, 50) implies (balance = 0 and previous_transaction = old - balance)
			invalid_stays: not is_valid_amount (amount) implies (balance = old balance and previous_transaction = old previous_transaction)

			modifies_clause: modify_model (["balance", "previous_transaction"], Current)
		end

	foreign_transfer (amount: INTEGER)
		local
			penalty, amount_with_penalty: INTEGER
		do
			penalty := (amount // 100) * 5
			amount_with_penalty := amount + penalty
			if is_valid_amount (amount_with_penalty) then
				if is_valid_balance_amount (balance, amount_with_penalty) then
					balance := balance - amount_with_penalty
					previous_transaction := - amount_with_penalty
				end
			end
		ensure
			is_valid_amount (amount + (amount // 100) * 5) and then is_valid_balance_amount (old balance, amount + (amount // 100) * 5) implies (balance = old balance - (amount + (amount // 100) * 5) and previous_transaction = - (amount + (amount // 100) * 5))
			is_valid_amount (amount + (amount // 100) * 5) and then not is_valid_balance_amount (old balance, amount + (amount // 100) * 5) implies (balance = old balance and previous_transaction = old previous_transaction)
			not is_valid_amount (amount + (amount // 100) * 5) implies (balance = old balance and previous_transaction = old previous_transaction)

			modifies_clause: modify_model (["balance", "previous_transaction"], Current)
		end

	foreign_deposit (amount: INTEGER)
		local
			penalty, amount_with_penalty: INTEGER
		do
			penalty := (amount // 100) * 5
			amount_with_penalty := amount - penalty
			if is_valid_amount (amount_with_penalty) then
				balance := balance + amount_with_penalty
				previous_transaction := amount_with_penalty
			end
		ensure
			is_valid_amount (amount - (amount // 100) * 5) implies (balance = old balance + (amount - (amount // 100) * 5) and previous_transaction = (amount - (amount // 100) * 5))
			not is_valid_amount (amount - (amount // 100) * 5) implies (balance = old balance and previous_transaction = old previous_transaction)

			modifies_clause: modify_model (["balance", "previous_transaction"], Current)
		end

	withdraw_by_cash_back (amount: INTEGER)
		local
			cashback, amount_with_cashback: INTEGER
		do
			cashback := (amount // 100) * 2
			amount_with_cashback := amount - cashback
			if is_valid_amount (amount_with_cashback) then
				if is_valid_balance_amount (balance, amount_with_cashback) then
					balance := balance - amount_with_cashback
					previous_transaction := - amount_with_cashback
				end
			end
		ensure
			is_valid_amount (amount - (amount // 100) * 2) and then is_valid_balance_amount (old balance, amount - (amount // 100) * 2) implies (balance = old balance - (amount - (amount // 100) * 2) and previous_transaction = - (amount - (amount // 100) * 2))
			is_valid_amount (amount - (amount // 100) * 2) and then not is_valid_balance_amount (old balance, amount - (amount // 100) * 2) implies (balance = old balance and previous_transaction = old previous_transaction)
			not is_valid_amount (amount - (amount // 100) * 2) implies (balance = old balance and previous_transaction = old previous_transaction)

			modifies_clause: modify_model (["balance", "previous_transaction"], Current)
		end

	atm_withdraw (amount: INTEGER)
		local
			atm_penalty, amount_with_penalty: INTEGER
		do
			atm_penalty := 4
			if is_valid_amount (amount) then
				amount_with_penalty := amount + atm_penalty
				if is_valid_balance_amount (balance, amount_with_penalty) then
					balance := balance - amount_with_penalty
					previous_transaction := - amount_with_penalty
				end
			end
		ensure
			valid_changes: is_valid_amount (amount) and then is_valid_balance_amount (old balance, amount + 4) implies (balance = old balance - (amount + 4) and previous_transaction = - (amount + 4))
			invalid_new_stays: is_valid_amount (amount) and then not is_valid_balance_amount (old balance, amount + 4) implies (balance = old balance and previous_transaction = old previous_transaction)
			invalid_stays: not is_valid_amount (amount) implies (balance = old balance and previous_transaction = old previous_transaction)

			modifies_clause: modify_model (["balance", "previous_transaction"], Current)
		end

	interest_after_year: INTEGER
		local
			interest, t: INTEGER
		do
			if balance <= 20_000 then
				interest := balance // 100
			elseif balance <= 160_000 then
				t := balance // 100
				interest := t * 2
			elseif balance <= 300_000 then
				t := balance // 100
				interest := t * 3
			else
				t := balance // 100
				interest := t * 4
			end
			Result := interest
		ensure
			less_2k: balance <= 20_000 implies Result = balance // 100
			from_20k: 20_000 < balance and balance <= 160_000 implies Result = (balance // 100) * 2
			from_160k: 160_000 < balance and balance <= 300_000 implies Result = (balance // 100) * 3
			from_300k: 300_000 < balance and balance <= {INTEGER}.max_value implies Result = (balance // 100) * 4
		end

	menu (option, amount: INTEGER): INTEGER
		note
			status: impure
		require
			option_1_to_9: 0 <= option and option <= 9
		do
			inspect option
			when 1 then
				deposit (amount)
				Result := get_balance
			when 2 then
				withdraw (amount)
				Result := get_balance
			when 3 then
				check_withdrawal (amount)
				Result := get_balance
			when 4 then
				Result := get_previous_transaction
			when 5 then
				foreign_transfer (amount)
				Result := get_balance
			when 6 then
				withdraw_by_cash_back (amount)
				Result := get_balance
			when 7 then
				foreign_deposit (amount)
				Result := get_balance
			when 8 then
				Result := interest_after_year
			when 9 then
				atm_withdraw (amount)
				Result := get_balance
			else
				Result := get_balance
			end
		ensure
			op1: option = 1 and is_valid_amount (amount)
				implies (balance = old balance + amount and previous_transaction = amount)
			op2: option = 2 and is_valid_amount (amount) and then is_valid_balance_amount (old balance, amount)
				implies (balance = old balance - amount and Result = balance and previous_transaction = - amount)
			op31: option = 3 and is_valid_amount (amount) and then is_valid_balance_amount (old balance, amount)
				implies (balance = old balance - amount and previous_transaction = - amount)
			op32: option = 3 and is_valid_amount (amount) and then not is_valid_balance_amount (old balance, amount) and then is_valid_balance_amount (old balance, 50)
				implies (balance = old balance - 50 and previous_transaction = -50)
			op33: option = 3 and then is_valid_amount (amount) and then not is_valid_balance_amount (old balance, amount) and not is_valid_balance_amount (old balance, 50)
				implies (balance = 0 and previous_transaction = old - balance)
			op4: option = 4 implies Result = previous_transaction
			o51: option = 5 and is_valid_amount (amount + (amount // 100) * 5) and then is_valid_balance_amount (old balance, amount + (amount // 100) * 5)
				implies (balance = old balance - (amount + (amount // 100) * 5) and previous_transaction = - (amount + (amount // 100) * 5))
			o52: option = 5 and is_valid_amount (amount + (amount // 100) * 5) and then not is_valid_balance_amount (old balance, amount + (amount // 100) * 5)
				implies (balance = old balance and previous_transaction = old previous_transaction)
			o61: option = 6 and is_valid_amount (amount - (amount // 100) * 2) and then is_valid_balance_amount (old balance, amount - (amount // 100) * 2)
				implies (balance = old balance - (amount - (amount // 100) * 2) and previous_transaction = - (amount - (amount // 100) * 2))
			o62: option = 6 and is_valid_amount (amount - (amount // 100) * 2) and then not is_valid_balance_amount (old balance, amount - (amount // 100) * 2)
				implies (balance = old balance and previous_transaction = old previous_transaction)
			o71: option = 7 and is_valid_amount (amount - (amount // 100) * 5)
				implies (balance = old balance + (amount - (amount // 100) * 5) and previous_transaction = (amount - (amount // 100) * 5))
			o81: option = 8 and balance <= 20_000 implies Result = balance // 100
			o82: option = 8 and 20_000 < balance and balance <= 160_000 implies Result = (balance // 100) * 2
			o83: option = 8 and 160_000 < balance and balance <= 300_000 implies Result = (balance // 100) * 3
			o84: option = 8 and 300_000 < balance and balance <= {INTEGER}.max_value implies Result = (balance // 100) * 4
			o9: option = 9 and is_valid_amount (amount) and then is_valid_balance_amount (old balance, amount + 4)
				implies (balance = old balance - (amount + 4) and previous_transaction = - (amount + 4))
			o0: option = 0 implies (balance = old balance and previous_transaction = old previous_transaction)

			modifies_clause: modify_model (["balance", "previous_transaction"], Current)
		end

invariant
	balance_not_negative: 0 <= balance

end
