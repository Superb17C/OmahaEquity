from itertools import combinations
from math import comb
from random import sample, shuffle
from termcolor import colored


# Adjustable parameters
num_ranks = 13
num_suits = 4
board_size = 5
holding_size = 4
num_players = 6


# Constants computed based on parameters
num_couplets_per_holding = int(holding_size * (holding_size - 1) / 2)
num_opponents = num_players - 1
num_opponents_couplets = num_opponents * num_couplets_per_holding


# Non-adjustable constants
ace = 12
king = 11
queen = 10
jack = 9
ten = 8
nine = 7
eight = 6
seven = 5
six = 4
five = 3
four = 2
three = 1
deuce = 0
deprecated_ace = -1
hearts = 3
spades = 2
diamonds = 1
clubs = 0
anything = 999


class Card:

    def __init__(self, rank, suit):
        self.rank = rank
        self.suit = suit

    def is_copy(self, target_card):
        return self.rank == target_card.rank and self.suit == target_card.suit

    def fulfills(self, target_card):
        rank_fulfills = target_card.rank == anything or self.rank == target_card.rank
        suit_fulfills = target_card.suit == anything or self.suit == target_card.suit
        return rank_fulfills and suit_fulfills

    def is_compatible(self, board):
        for target_card in board:
            if self.is_copy(target_card):
                return False
        return True

    def str(self):
        return rank_to_str(self.rank) + suit_to_str(self.suit)


class Couplet: # a couplet is two cards that form a subset of a player's holding

    def __init__(self, card_1, card_2):
        self.card_1 = card_1
        self.card_2 = card_2

    def fulfills(self, target_couplet):
        fulfills_in_order = self.card_1.fulfills(target_couplet.card_1) and self.card_2.fulfills(target_couplet.card_2)
        fulfills_out_of_order = self.card_1.fulfills(target_couplet.card_2) and self.card_2.fulfills(target_couplet.card_1)
        return fulfills_in_order or fulfills_out_of_order

    def is_compatible(self, board):
        return self.card_1.is_compatible(board) and self.card_2.is_compatible(board)

    def str(self):
        return self.card_1.str() + " " + self.card_2.str()


def rank_to_str(rank):
    if rank == ace or rank == deprecated_ace:
        return "A"
    elif rank == king:
        return "K"
    elif rank == queen:
        return "Q"
    elif rank == jack:
        return "J"
    elif rank == ten:
        return "\u042E"
    elif rank <= nine and rank >= deuce:
        return str(rank + 2)
    else: # rank == anything
        return "X"


def suit_to_str(suit):
    if suit == hearts:
        return colored("\u2665", "red")
    elif suit == spades:
        return "\u2660"
    elif suit == diamonds:
        return colored("\u2666", "blue")
    elif suit == clubs:
        return colored("\u2663", "green")
    else: # suit == anything
        return colored("\u00D7", "yellow")


def rank_range():
    return reversed(range(num_ranks))


def suit_range():
    return reversed(range(num_suits))


def assemble_deck():
    deck = []
    for rank in rank_range(): # reversing ensures that higher-ranked cards are assessed first
        for suit in suit_range():
            deck.append(Card(rank, suit))
    return deck


def deal_random_cards(num_cards, deck):
    shuffle(deck)
    return sample(deck, num_cards)


def print_cards(cards, label=""):
    cards_str = label
    for card in cards:
        cards_str += card.str() + " "
    print(cards_str)


def partition_by_suit(board):
    return [[card for card in board if card.suit == suit] \
            for suit in suit_range()]


def extract_ranks(board, include_deprecation):
    board_ranks = [card.rank for card in board]
    if include_deprecation:
        board_ranks += [deprecated_ace for rank in board_ranks if rank == ace]
    return board_ranks


def tally_ranks(board):
    board_ranks = extract_ranks(board, False)
    rank_tallies = {rank: 0 for rank in rank_range()}
    for board_rank in board_ranks:
        rank_tallies[board_rank] += 1
    return rank_tallies


def max_tally(rank_tallies): # used for determining whether the board is paired, tripled, etc.
    most_of_one_rank = 0
    for rank in rank_range():
        rank_tally = rank_tallies[rank]
        if rank_tally > most_of_one_rank:
            most_of_one_rank = rank_tally
    return most_of_one_rank


def highest_repeated_rank(rank_tallies):
    for rank in rank_range():
        rank_tally = rank_tallies[rank]
        if rank_tally > 1:
            return rank
    return None # should never get this far as long as function is called only when board is paired


# Construct a couplet whose cards share the given rank
def pair_couplet(rank):
    return Couplet(Card(rank, anything), Card(rank, anything))


# Convert the (first) two cards in a list-of-cards into a couplet
def couplify(cards):
    return Couplet(cards[0], cards[1])


# Convert the (first) two ranks in a list-of-ranks into a couplet
def couplify_ranks(ranks, suit):
    return Couplet(Card(ranks[0] % num_ranks, suit), Card(ranks[1] % num_ranks, suit)) # modulo undeprecates any Aces


def remove_incompatible_couplets(level, forbidden_cards):
    return [couplet for couplet in level if couplet.is_compatible(forbidden_cards)]


def index_of_level_containing(target_couplet, levels):
    for level_index in range(len(levels)):
        level = levels[level_index]
        for couplet in level:
            if target_couplet.fulfills(couplet):
                return level_index
    return None # should never get here given how/where this function is used in this program


def subsets_of_size(n, zet):
    return list(combinations(zet, n))


def flatten(lizt):
    flat_list = []
    for sublist in lizt:
        flat_list += sublist
    return flat_list


def all_levels(board): # a level is a list of 1 or more couplets that, given the board cards, form a hand of equal value
    return straight_flush_levels(board) + \
           four_of_a_kind_levels(board) + \
           full_house_levels(board) + \
           flush_levels(board) + \
           straight_levels(board) + \
           three_of_a_kind_levels(board) + \
           two_pair_levels(board) + \
           one_pair_levels(board) + \
           high_card_levels(board) + \
           [[Couplet(Card(anything, anything), Card(anything, anything))]] # emergency catch-all; all possible holdings should qualify for a level above this line


def straight_flush_levels(board): # for boards longer than 5 cards, this function is sensitive to the relative "highness" of the suits
    levels = []
    for subboard in partition_by_suit(board):
        if len(subboard) >= 3:
            subboard_suit = subboard[0].suit
            levels += straight_levels_with_suit(subboard, subboard_suit)
    '''return levels''' # version that allows duplicate cards
    return remove_empty_levels([remove_incompatible_couplets(inner_level, board) \
                                for inner_level in levels]) # version that assumes no duplicate cards


def four_of_a_kind_levels(board):
    levels = []
    rank_tallies = tally_ranks(board)
    for rank in rank_range():
        rank_tally = rank_tallies[rank]
        if rank_tally == 2:
            levels.append([pair_couplet(rank)])
        elif rank_tally >= 3:
            levels.append([Couplet(Card(rank, anything), Card(anything, anything))])
    return levels


def full_house_levels(board):
    levels = []
    rank_tallies = tally_ranks(board)
    most_of_one_rank = max_tally(rank_tallies)
    if most_of_one_rank == 2:
        for rank in rank_range(): # first check for all the ways to make Aces full, then Kings full, Queens full, etc.
            rank_tally = rank_tallies[rank]
            if rank_tally == 1:
                levels.append([pair_couplet(rank)])
            elif rank_tally == 2:
                [levels.append([Couplet(Card(rank, anything), Card(inner_rank, anything))]) \
                 for inner_rank in rank_range() \
                 if (rank_tallies[inner_rank] == 1) or (rank_tallies[inner_rank] == 2 and inner_rank < rank)]
                # the second condition ensures that, on a double-paired board, a couplet matching both pairs counts as high-full-of-low rather than low-full-of-high
    elif most_of_one_rank >= 3:
        continue_scan = True
        for rank in rank_range():
            if continue_scan:
                rank_tally = rank_tallies[rank]
                if rank_tally == 1:
                    levels.append([pair_couplet(rank)])
                elif rank_tally >= 3: # the rank tally of 2 can be skipped, since it always makes quads rather than a full house
                    [levels.append([pair_couplet(inner_rank)]) \
                     for inner_rank in rank_range() \
                     if (rank_tallies[inner_rank] == 0) or (rank_tallies[inner_rank] == 1 and inner_rank < rank)]
                    continue_scan = False # all pocket pairs lower than the board triple are assessed in this iteration and therefore do not need to appear in a future full house level
    return levels # skips all of the above steps and returns no levels if board is not at least paired


def flush_levels(board): # for boards longer than 5 cards, this function is sensitive to the relative "highness" of the suits
    levels = []
    for subboard in partition_by_suit(board):
        if len(subboard) >= 3:
            subboard_suit = subboard[0].suit
            '''[levels.append([Couplet(Card(rank, subboard_suit), Card(anything, subboard_suit))]) \
             for rank in rank_range()]''' # version that allows duplicate cards in deck
            for novel_rank in [rank \
                               for rank in reversed(range(three, num_ranks)) \
                               if rank not in extract_ranks(subboard, False)]: # no suited couplet is lower than Three-high; also, this line assumes no card appears more than once in the deck
                levels.append([Couplet(Card(novel_rank, subboard_suit), Card(anything, subboard_suit))]) # version that disallows duplicate cards in deck
    return levels


def straight_levels(board):
    return straight_levels_with_suit(board, anything)


def straight_levels_with_suit(board, suit_to_record): # may output the same couplet in multiple levels, but this is OK
    levels = []
    unique_board_ranks = []
    [unique_board_ranks.append(rank) for rank in extract_ranks(board, True) if rank not in unique_board_ranks]
    for rank in reversed(range(five, num_ranks)): # when allowing exactly 1 rank (Ace) to be deprecated, a Five-high straight is the lowest possible straight
        levels.append(straight_level_with_suit(rank, unique_board_ranks, suit_to_record))
    return remove_empty_levels(levels)


# List all couplets which form a [high_rank]-high straight given the board
def straight_level_with_suit(high_rank, board_ranks, suit_to_record):
    straight_ranks = [rank for rank in reversed(range(high_rank - 4, high_rank + 1))] # list all ranks which make up a [high_rank]-high straight, in descending order
    return [couplify_ranks([rank \
                            for rank in straight_ranks \
                            if rank not in subset], suit_to_record) \
            for subset in subsets_of_size(3, sorted(board_ranks, reverse=True)) \
            if subset in subsets_of_size(3, straight_ranks)]


def three_of_a_kind_levels(board):
    levels = []
    rank_tallies = tally_ranks(board)
    most_of_one_rank = max_tally(rank_tallies)
    if most_of_one_rank == 1:
        for rank in rank_range():
            rank_tally = rank_tallies[rank]
            if rank_tally == 1:
                levels.append([pair_couplet(rank)])
    elif most_of_one_rank == 2:
        for rank in rank_range():
            rank_tally = rank_tallies[rank]
            if rank_tally == 2:
                [levels.append([Couplet(Card(rank, anything), Card(inner_rank, anything))]) \
                 for inner_rank in rank_range() \
                 if rank_tallies[inner_rank] == 0]
    elif most_of_one_rank >= 3:
        continue_scan = True
        tally_2_overranks = [] # will soon contain the rank of all board pairs higher than the highest board trips
        for rank in rank_range(): # check for trip Aces first, then trip Kings, Queens, etc.
            if continue_scan:
                rank_tally = rank_tallies[rank]
                if rank_tally == 2: # can skip rank tally of 1 because it always makes a full house rather than trips
                    [levels.append([Couplet(Card(rank, anything), Card(inner_rank, anything))]) \
                     for inner_rank in rank_range() \
                     if rank_tallies[inner_rank] == 0]
                    tally_2_overranks.append(rank)
                elif rank_tally == 3:
                    higher_kicker_rank_range = [inner_rank \
                                                for inner_rank in rank_range() \
                                                if inner_rank != rank and inner_rank not in tally_2_overranks]
                    for higher_kicker_rank in higher_kicker_rank_range:
                        lower_kicker_rank_range = [inner_rank \
                                                   for inner_rank in higher_kicker_rank_range \
                                                   if inner_rank < higher_kicker_rank]
                        for lower_kicker_rank in lower_kicker_rank_range:
                            levels.append([Couplet(Card(higher_kicker_rank, anything), Card(lower_kicker_rank, anything))])
                    continue_scan = False
    return levels


def two_pair_levels(board):
    levels = []
    rank_tallies = tally_ranks(board)
    most_of_one_rank = max_tally(rank_tallies)
    if most_of_one_rank == 1:
        higher_pair_rank_range = [rank for rank in rank_range() if rank_tallies[rank] == 1]
        for higher_pair_rank in higher_pair_rank_range:
            lower_pair_rank_range = [rank for rank in higher_pair_rank_range if rank < higher_pair_rank]
            for lower_pair_rank in lower_pair_rank_range:
                levels.append([Couplet(Card(higher_pair_rank, anything), Card(lower_pair_rank, anything))])
    elif most_of_one_rank == 2:
        board_pair_rank = highest_repeated_rank(rank_tallies)
        for rank in rank_range():
            rank_tally = rank_tallies[rank]
            if rank_tally == 0:
                levels.append([pair_couplet(rank)])
            if rank_tally == 1:
                [levels.append([Couplet(Card(rank, anything), Card(inner_rank, anything))]) \
                 for inner_rank in rank_range() \
                 if inner_rank > board_pair_rank and rank_tallies[inner_rank] == 1 and inner_rank != rank]
                [levels.append([Couplet(Card(rank, anything), Card(inner_rank, anything))]) \
                 for inner_rank in rank_range() \
                 if inner_rank < board_pair_rank or rank_tallies[inner_rank] == 0]
    return levels


def one_pair_levels(board):
    levels = []
    rank_tallies = tally_ranks(board)
    most_of_one_rank = max_tally(rank_tallies)
    if most_of_one_rank == 1:
        for rank in rank_range():
            rank_tally = rank_tallies[rank]
            if rank_tally == 0:
                levels.append([pair_couplet(rank)])
            if rank_tally == 1:
                [levels.append([Couplet(Card(rank, anything), Card(inner_rank, anything))]) \
                 for inner_rank in rank_range() \
                 if rank_tallies[inner_rank] == 0]
    elif most_of_one_rank == 2:
        higher_kicker_rank_range = [rank for rank in rank_range() if rank_tallies[rank] == 0]
        for higher_kicker_rank in higher_kicker_rank_range:
            lower_kicker_rank_range = [rank for rank in higher_kicker_rank_range if rank < higher_kicker_rank]
            for lower_kicker_rank in lower_kicker_rank_range:
                levels.append([Couplet(Card(higher_kicker_rank, anything), Card(lower_kicker_rank, anything))])
    return levels


def high_card_levels(board):
    levels = []
    rank_tallies = tally_ranks(board)
    most_of_one_rank = max_tally(rank_tallies)
    if most_of_one_rank == 1:
        higher_kicker_rank_range = [rank for rank in rank_range() if rank_tallies[rank] == 0]
        for higher_kicker_rank in higher_kicker_rank_range:
            lower_kicker_rank_range = [rank for rank in higher_kicker_rank_range if rank < higher_kicker_rank]
            for lower_kicker_rank in lower_kicker_rank_range:
                levels.append([Couplet(Card(higher_kicker_rank, anything), Card(lower_kicker_rank, anything))])
    return levels


def print_levels(levels):
    for level in levels:
        level_string = ""
        for couplet in level:
            level_string += couplet.str() + "   "
        print(level_string)


def remove_empty_levels(levels):
    return [level for level in levels if len(level) > 0]


# Explicitly list out all couplets belonging to each level, resolving all uses of the "anything" keyword
def specify(generic_levels, board):
    deck = [card for card in assemble_deck() if card.is_compatible(board)]
    specific_couplets = [couplify(subset) for subset in subsets_of_size(2, deck)]
    specific_levels = [[] for level in generic_levels]
    for specific_couplet in specific_couplets:
        continue_scan = True
        for level_index in range(len(generic_levels)):
            generic_level = generic_levels[level_index]
            for generic_couplet in generic_level:
                if continue_scan and specific_couplet.fulfills(generic_couplet):
                    specific_levels[level_index].append(specific_couplet)
                    continue_scan = False
    return remove_empty_levels(specific_levels)


# Compute what fraction of the pot a player with the given holding can expect to win on the given board on average
def utility(holding, board):
    levels = specify(all_levels(board), board)
    best_level_index = len(levels) # dummy initial value
    for couplet in [couplify(subset) for subset in subsets_of_size(2, holding)]:
        level_index = index_of_level_containing(couplet, levels)
        if level_index < best_level_index: # the earlier a couplet appears in the level list, the better it is
            best_level_index = level_index
    num_better_couplets = len(remove_incompatible_couplets(flatten(levels[:best_level_index]), holding))
    num_equipotent_couplets = len(remove_incompatible_couplets(levels[best_level_index], holding))
    num_worse_couplets = len(remove_incompatible_couplets(flatten(levels[best_level_index + 1:]), holding))
    prob_best_hand = comb(num_equipotent_couplets + num_worse_couplets, num_opponents_couplets) / \
                     comb(num_better_couplets + num_equipotent_couplets + num_worse_couplets, num_opponents_couplets) \
        # probability that none of the opponents' couplets form a better hand, assuming random distribution of couplets
    expected_pot_fraction_given_best_hand = 0
    try:
        for num_equipotent_opponents_couplets in range(min(num_equipotent_couplets + 1, num_opponents_couplets + 1)):
            num_worse_opponents_couplets = num_opponents_couplets - num_equipotent_opponents_couplets
            prob_num_equipotent_opponents_couplets = comb(num_equipotent_couplets, num_equipotent_opponents_couplets) * \
                                                     comb(num_worse_couplets, num_worse_opponents_couplets) / \
                                                     comb(num_equipotent_couplets + num_worse_couplets, num_opponents_couplets) \
                # probability that exactly [num] opponent couplets tie with you for the best hand
            num_winners = num_equipotent_opponents_couplets + 1
            expected_pot_fraction_given_best_hand += prob_num_equipotent_opponents_couplets / num_winners
    except ZeroDivisionError: # this error occurs whenever there exist fewer equipotent-or-worse couplets than opponents' couplets
        pass # leave expected pot fraction at 0 (its initial value), thereby allowing the return value to be 0
    return prob_best_hand * expected_pot_fraction_given_best_hand


'''test_board = deal_random_cards(board_size, assemble_deck())
print_cards(test_board, "Board: ")
print("")
generic_levels = all_levels(test_board)
#print_levels(generic_levels)
print("")
specific_levels = specify(generic_levels, test_board)
print_levels(specific_levels)
print("")
u = 0
while u < 1:
    test_holding = deal_random_cards(holding_size, [card for card in assemble_deck() if card.is_compatible(test_board)])
    u = utility(test_holding, test_board)
print_cards(test_holding, "Holding: ")
print("Utility: " + str(u))'''


num_trials = 25000
test_holding = [Card(ace, hearts), \
                Card(king, clubs), \
                Card(queen, clubs), \
                Card(ten, hearts)]
print_cards(test_holding, "Holding: ")
print("")
sum_utilities = 0
for trial_index in range(num_trials):
    test_board = deal_random_cards(board_size, [card for card in assemble_deck() if card.is_compatible(test_holding)])
    test_utility = utility(test_holding, test_board)
    sum_utilities += test_utility
    print_cards(test_board, "Trial " + str(trial_index + 1) + ": Utility is " + str(test_utility) + " on board ")
print("")
avg_utility = sum_utilities / num_trials
print_cards(test_holding, "Holding: ")
print("Average utility over " + str(num_trials) + " trials is " + str(avg_utility))


# to-do: make 4oak function independent of num_suits; make 5oak function; short deck