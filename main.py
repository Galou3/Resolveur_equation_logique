import copy
import numpy as np
from random import *


def generate_problem(nb_clause, nb_litteraux):
    problem = [[] for i in range(nb_clause)]
    for i in range(nb_clause):
        a = randint(1, nb_litteraux)
        while len(problem[i]) < a:
            b = randint(1, nb_litteraux)
            if not (b in problem[i]):
                problem[i].append(b)
    return problem


def popall(liste, a):
    while a in liste:
        liste.remove(a)
    return liste


class DPLL:
    def __init__(self, problem):
        self.problem = problem
        self.n = len(problem)
        self.litteraux_present = []
        for clause in self.problem:
            for elt in clause:
                if not (elt in self.litteraux_present):
                    self.litteraux_present.append(elt)
        self.litteraux_purs = []
        for i in self.litteraux_present:
            if i % 2 == 1 and not (i + 1 in self.litteraux_present):
                self.litteraux_purs.append(i)
            if i % 2 == 0 and not (i - 1 in self.litteraux_present):
                self.litteraux_purs.append(i)
                #
        self.litteraux = self.litteraux_present.copy()
        for lit in self.litteraux_present:
            if lit % 2 == 0 and not (lit - 1 in self.litteraux):
                self.litteraux.append(lit - 1)
            if lit % 2 == 1 and not (lit + 1 in self.litteraux):
                self.litteraux.append(lit + 1)
                #
        self.litteraux.sort()
        max = self.litteraux[-1]
        self.litteraux = [i for i in range(1, max + 1)]
        self.nb_literraux = len(self.litteraux)
        self.etat_clauses = [0 for i in range(self.n)]
        self.long_clauses = [len(self.problem[i]) for i in range(self.n)]
        self.etat_variables = [0 for i in range(self.nb_literraux + 1)]
        self.pile = []
        self.literraux_clauses = [[] for i in range(self.nb_literraux + 1)]
        self.historique = []
        self.litteraux_backtrack = []
        self.solutions = []
        for i in range(self.n):
            for j in self.problem[i]:
                self.literraux_clauses[j].append(i)

    def if_mono_lit(self, clause):
        p = None
        for i in range(
                len(self.problem[clause])
        ):  # recherche mono litteral de quel litteral
            if self.etat_variables[self.problem[clause][i]] == 0:
                p = self.problem[clause][i]
        if p % 2 == 1:
            self.etat_clauses[clause] = p  # La clause i devient vraie par rapport p
            for j in self.literraux_clauses[p + 1]:
                self.long_clauses[
                    j
                ] -= 1  # On enleve les p barre dans les autres clauses
            self.etat_variables[p], self.etat_variables[p + 1] = (
                1,
                1,
            )  # On dit que p et p barre sont affectées
            self.pile.append([p, 1])
            # self.pile.append([p+1,0])        #On dit qu'on a affecté Faux au littéral p+1
            for j in self.literraux_clauses[p]:
                if self.etat_clauses[j] == 0:
                    self.etat_clauses[
                        j
                    ] = p  # On met vrai toutes les clauses qui contiennent p et qui sont pas déjà vrai
        else:
            self.etat_variables[p], self.etat_variables[p - 1] = (
                1,
                1,
            )  # On dit qu'on a affecté une valeur a p barre et p
            self.pile.append([p, 1])  # p barre devient vraie
            # self.pile.append([p-1, 0])       # p devient faux
            for j in self.literraux_clauses[p - 1]:
                self.long_clauses[j] -= 1  # On enleve une longueur la où y'a des p
            self.etat_clauses[
                clause
            ] = p  # La clause i est vrai par rapport au littéral p
            for j in self.literraux_clauses[p]:
                if self.etat_clauses[j] == 0:
                    self.etat_clauses[
                        j
                    ] = p  # On met vrai toutes les clauses qui contiennent p barre et qui sont pas déjà vrai

    def search_mono_lit(self):
        for i in range(self.n):
            if self.long_clauses[i] == 1 and self.etat_clauses[i] == 0:
                return i
        return -1

    def elimine_mono_lit(self):
        clause = self.search_mono_lit()
        while clause != -1:
            p = None
            for i in range(
                    len(self.problem[clause])
            ):  # recherche mono litteral de quel litteral
                if self.etat_variables[self.problem[clause][i]] == 0:
                    p = self.problem[clause][i]
            self.change_litteral_true(p)
            clause = self.search_mono_lit()

    def fail_first(self):  # choisi le litteral dont l'opposé apparait le plus
        copie = copy.deepcopy(self.literraux_clauses)
        liste = [[i] for i in range(1, self.nb_literraux + 1)]
        for i in range(1, self.nb_literraux + 1):
            if self.etat_variables[i] == 0:
                for j in self.literraux_clauses[i]:
                    if self.etat_clauses[j] != 0:
                        copie[i].remove(j)
                liste[i - 1].append(len(copie[i]))

            else:
                liste[i - 1].append(-1)
        max = liste[0][1]
        index_max = 0
        for j in range(len(liste)):
            if max < liste[j][1]:
                max = liste[j][1]
                index_max = j
        p = liste[index_max][0]
        if p % 2 == 0:
            return p - 1
        else:
            return p + 1

    def satisfy_first(self):  # choisit le litteral qui apparait le plus
        copie = copy.deepcopy(self.literraux_clauses)
        liste = [[i] for i in range(1, self.nb_literraux + 1)]
        for i in range(1, self.nb_literraux + 1):
            if self.etat_variables[i] == 0:
                for j in self.literraux_clauses[i]:
                    if self.etat_clauses[j] != 0:
                        copie[i].remove(j)
                liste[i - 1].append(len(copie[i]))
            else:
                liste[i - 1].append(-1)
        max = liste[0][1]
        index_max = 0
        for j in range(len(liste)):
            if max < liste[j][1]:
                max = liste[j][1]
                index_max = j
        return liste[index_max][0]

    def choix_variable(self):
        for i in range(1, self.nb_literraux):
            if self.etat_variables[i] == 0:
                return self.litteraux[i]

    def change_litteral_true(self, p):  # change le litteral p en vrai
        self.historique.append(
            [
                p,
                1,
                self.etat_clauses.copy(),
                self.etat_variables.copy(),
                self.long_clauses.copy(),
                self.pile.copy(),
            ]
        )  # Rajoutes l'historique pour p vrai
        if p % 2 == 1:
            self.etat_variables[p], self.etat_variables[p + 1] = (
                1,
                1,
            )  # On dit que p et p barre sont affectées
            for j in self.literraux_clauses[p + 1]:
                self.long_clauses[
                    j
                ] -= 1  # On enleve les p barre dans les autres clauses

        else:
            self.etat_variables[p], self.etat_variables[p - 1] = (
                1,
                1,
            )  # On dit que p et p barre sont affectées

            for j in self.literraux_clauses[p - 1]:
                self.long_clauses[
                    j
                ] -= 1  # On enleve une longueur la où y'a des p

        self.pile.append([p, 1])  # p barre devient vraie

        for clause in self.literraux_clauses[
            p
        ]:  # On prend chaque clause qui contient p

            if (
                    self.etat_clauses[clause] == 0
            ):  # Si la clause n'est toujours pas passé vraie :
                self.etat_clauses[
                    clause
                ] = p  # La clause devient vrai par rapport à p

    def simplification_2(
            self,
    ):  # Fct qui permet de savoir si un lit est soit que vrai soit que faux
        litteraux_present = []
        for clause in self.problem:
            for elt in clause:
                if not (elt in litteraux_present):
                    litteraux_present.append(elt)
        Monolit = []
        for i in litteraux_present:
            if i % 2 == 1 and not (i + 1 in litteraux_present):
                Monolit.append(i)
            if i % 2 == 0 and not (i - 1 in litteraux_present):
                Monolit.append(i)
        return Monolit

    def backtrap(self):  # Si y'a une longueur de clause = 0 on fait ça
        A = self.historique[-1][0]
        self.etat_clauses = self.historique[-1][2]
        self.etat_variables = self.historique[-1][3]
        self.long_clauses = self.historique[-1][4]
        self.pile = self.historique[-1][-1]
        self.historique = self.historique[0:-1]
        self.litteraux_backtrack.append(A)
        if A % 2 == 1:
            if not (
                    A + 1 in self.litteraux_backtrack
            ):  # Si on a pas encore essayé de changer la valeur
                self.change_litteral_true(A + 1)
            else:
                if len(self.pile) == 0:
                    self.pile.append("NO SOLUTION")
                    self.etat_clauses = [1 for i in range(self.n)]
                    self.long_clauses = [1 for i in range(self.n)]
                    p = 0
                else:
                    p = 1
                    while p == 1:
                        if len(self.pile) == 0:
                            self.pile.append("NO SOLUTION")
                            self.etat_clauses = [1 for i in range(self.n)]
                            self.long_clauses = [1 for i in range(self.n)]
                            p = 0
                        else:
                            lit = self.pile[-1][0]
                            popall(self.litteraux_backtrack, A)
                            if A % 2 == 1:
                                popall(self.litteraux_backtrack, A + 1)
                            else:
                                popall(self.litteraux_backtrack, A - 1)
                            A = lit
                            lit_b = 0
                            if lit % 2 == 0:
                                lit_b = lit - 1
                            else:
                                lit_b = lit + 1
                            if not (lit_b in self.litteraux_backtrack):
                                p = 0
                                self.litteraux_backtrack.append(lit)
                            else:
                                if not (lit in self.litteraux_backtrack):
                                    self.litteraux_backtrack.append(lit)
                            self.etat_clauses = self.historique[-1][2]
                            self.etat_variables = self.historique[-1][3]
                            self.long_clauses = self.historique[-1][4]
                            self.pile = self.historique[-1][-1]

                            self.historique = self.historique[0:-1]
                    if not (self.pile == ['NO SOLUTION']):
                        if lit % 2 == 1:
                            self.change_litteral_true(lit + 1)
                            self.litteraux_backtrack.append(lit + 1)
                        else:
                            self.change_litteral_true(lit - 1)
                            self.litteraux_backtrack.append(lit - 1)
        else:
            if not (A - 1 in self.litteraux_backtrack):
                self.change_litteral_true(A - 1)
            else:
                if len(self.pile) == 0:
                    self.pile.append("NO SOLUTION")
                    self.etat_clauses = [1 for i in range(self.n)]
                    self.long_clauses = [1 for i in range(self.n)]
                # elif len(self.pile) == 0 and self.solutions != [] :
                #     pass
                else:
                    p = 1
                    while p == 1:
                        if self.pile == []:
                            self.pile.append("NO SOLUTION")
                            self.etat_clauses = [1 for i in range(self.n)]
                            self.long_clauses = [1 for i in range(self.n)]
                            p = 0
                        else:
                            lit = self.pile[-1][0]
                            lit_b = 0
                            if lit % 2 == 0:
                                lit_b = lit - 1
                            else:
                                lit_b = lit + 1
                            if not (lit_b in self.litteraux_backtrack):
                                p = 0
                                self.litteraux_backtrack.append(lit)
                            else:
                                if not (lit in self.litteraux_backtrack):
                                    self.litteraux_backtrack.append(lit)
                            popall(self.litteraux_backtrack, A)
                            if A % 2 == 1:
                                popall(self.litteraux_backtrack, A + 1)
                            else:
                                popall(self.litteraux_backtrack, A - 1)
                            self.etat_clauses = self.historique[-1][2]
                            self.etat_variables = self.historique[-1][3]
                            self.long_clauses = self.historique[-1][4]
                            self.pile = self.historique[-1][-1]
                            A = self.historique[-1][0]
                            self.historique = self.historique[0:-1]
                    if not (self.pile == ['NO SOLUTION']):
                        if lit % 2 == 1:
                            self.change_litteral_true(lit + 1)
                            self.litteraux_backtrack.append(lit + 1)
                        else:
                            self.change_litteral_true(lit - 1)
                            self.litteraux_backtrack.append(lit - 1)

    def resolve_1_solution(self, heuristic=None):
        p = 1
        while p == 1:
            q = 1
            p = 0
            if len(self.litteraux_purs) != 0:
                for A in self.litteraux_purs:
                    if self.etat_variables[A] == 0:
                        self.change_litteral_true(A)
                        self.litteraux_purs.remove(A)
                        break
            else:
                A = self.search_mono_lit()
                if A != -1:
                    lit = None
                    for i in range(
                            len(self.problem[A])
                    ):  # recherche mono litteral de quel litteral
                        if self.etat_variables[self.problem[A][i]] == 0:
                            lit = self.problem[A][i]
                    self.change_litteral_true(lit)
                else:
                    if heuristic is None:
                        A = self.choix_variable()
                    elif heuristic == 1:
                        A = self.fail_first()
                    elif heuristic == 2:
                        A = self.satisfy_first()
                    self.change_litteral_true(A)  # On change le litteral A en vrai
            while q == 1:
                q = 0
                for i in range(len(self.long_clauses)):
                    if (
                            self.long_clauses[i] == 0
                    ):  # Si on a une clause de longueur vide, on a fait de la merde
                        self.backtrap()
                        q = 1
                        if self.pile[-1] != "NO SOLUTION":
                            p = 1
                        else:
                            p = 0
                        break
                for j in range(len(self.etat_clauses)):
                    if (
                            self.etat_clauses[j] == 0
                    ):  # Si y'a encore des clauses non résolus, on refait un tour
                        p = 1
                        break

    def liste_all_solution(self):
        liste = []
        for sol in self.solutions:
            if len(sol) == self.nb_literraux / 2:
                liste.append(sol)
            else:
                lit_affect = [sol[i][0] for i in range(len(sol))]
                sol1 = copy.deepcopy(sol)
                lit_affect1 = lit_affect.copy()
                for i in range(len(lit_affect)):
                    if lit_affect[i] % 2 == 0:
                        lit_affect1.append(lit_affect[i] - 1)
                    else:
                        lit_affect1.append(lit_affect[i] + 1)
                nb_lit_manq = self.nb_literraux / 2 - len(sol)
                # Je prends uniquement les impair et je fais des combinaisons de faux vrai.
                for i in range(1, len(self.litteraux), 2):
                    if not (i in lit_affect1):
                        sol1.append()

    def resolve_all_solutions(self, heuristic=None):
        p = 1
        while p == 1:
            q = 1
            p = 0
            if len(self.litteraux_purs) != 0:
                for A in self.litteraux_purs:
                    if self.etat_variables[A] == 0:
                        self.change_litteral_true(A)
                        self.litteraux_purs.remove(A)
                        break
            else:
                A = self.search_mono_lit()
                if A != -1:
                    lit = None
                    for i in range(
                            len(self.problem[A])
                    ):  # recherche mono litteral de quel litteral
                        if self.etat_variables[self.problem[A][i]] == 0:
                            lit = self.problem[A][i]
                    if not (lit in self.litteraux_backtrack):
                        self.change_litteral_true(lit)
                else:
                    if heuristic is None:
                        A = self.choix_variable()
                    elif heuristic == 1:
                        A = self.fail_first()
                    elif heuristic == 2:
                        A = self.satisfy_first()
                    self.change_litteral_true(A)  # On change le litteral A en vrai
            while q == 1:
                q = 0
                for i in range(len(self.long_clauses)):
                    if (
                            self.long_clauses[i] == 0
                    ):  # Si on a une clause de longueur vide, on a fait de la merde
                        self.backtrap()
                        q = 1
                        if self.pile != ["NO SOLUTION"]:
                            p = 1
                        else:
                            p = 0
                        break
                for i in self.litteraux:
                    if self.etat_variables[i] == 0:
                        for j in range(len(self.etat_clauses)):
                            if (
                                    self.etat_clauses[j] == 0
                            ):  # Si y'a encore des clauses non résolus, on refait un tour sauf si toute les variables ont déjà été affectés
                                p = 1
                                break

                if q == 0 and p == 0:
                    if not (0 in self.etat_clauses):
                        self.solutions.append(self.pile)
                    if self.pile != ["NO SOLUTION"]:
                        self.backtrap()
                        q = 1
                    else:
                        if len(self.solutions) > 1:
                            self.solutions = self.solutions[:-1]

    def nbr_sol(self):
        cpt = 0
        if self.solutions[0] == ['NO SOLUTION']:
            return 0
        else:
            for sol in self.solutions:
                taille = self.nb_literraux // 2 - len(sol)
                cpt += 2 ** taille
        return cpt


# Générateurs :
def pigeon(n):
    literals = [i for i in range(1, 2 * n * (n - 1) + 1)]
    literals_sorted = []
    cnf = []

    '''Au moins un pigeon par cage'''

    for i in range(n):
        clause = []
        for j in range(n - 1):
            clause.append(literals[2 * (i * (n - 1) + j)])
        cnf.append(clause)

    for i in range(n - 1):
        cage = []
        for j in range(n):
            cage.append(literals[2 * (j * (n - 1) + i)])
        literals_sorted.append(cage)

    '''Au plus une cage par pigeon'''

    for i in range(n):
        for j in range(n - 1):
            for k in range(n - j - 2):
                clause = [literals[2 * (i * (n - 1) + j) + 1], literals[2 * (i * (n - 1) + j + k + 1) + 1]]
                cnf.append(clause)

    '''Au plus un pigeon par cage'''

    for i in range(n - 1):
        for j in range(n):
            for k in range(n - j - 1):
                clause = [1 + literals_sorted[i][j], 1 + literals_sorted[i][j + k + 1]]
                cnf.append(clause)

    return cnf


def dames(n):
    litterals = [i for i in range(1, 2 * (n ** 2) + 1)]
    cnf = []

    for j in range(n):  # j colonne
        clause = []
        for i in range(n):  # i ligne
            # au moins une dame par ligne
            clause.append(litterals[2 * j + 2 * n * i])
            for k in range(i + 1, n):
                # max une dame par ligne
                clause_dame_ligne = [litterals[2 * j + 2 * i * n + 1], litterals[2 * j + 2 * k * n + 1]]

                cnf.append(clause_dame_ligne)
                # chaque ligne a au plus une dame
                clause_ligne = [litterals[2 * j * n + 2 * i + 1], litterals[2 * j * n + 2 * k + 1]]
                cnf.append(clause_ligne)
        cnf.append(clause)

    for i in range(n):
        for j in range(n - i):
            for k in range(j + 1, n - i):
                diag_jj = j * (n + 1)
                diag_kk = k * (n + 1)
                anti_diag_jj = j + (n - 1 - j) * n
                anti_diag_kk = k + (n - 1 - k) * n
                # diag principale
                if i == 0:  # Ne pas compter 2 fois les clauses concernant principales
                    # Diagonale principale
                    clause = [litterals[2 * diag_jj + 1], litterals[2 * diag_kk + 1]]
                    cnf.append(clause)
                    # Antidiagonale principale
                    clause = [litterals[2 * anti_diag_jj + 1], litterals[2 * anti_diag_kk + 1]]
                    cnf.append(clause)
                if i != 0:
                    # Diagonales inf
                    clause = [litterals[2 * diag_jj + 2 * i * n + 1], litterals[2 * diag_kk + 2 * i * n + 1]]
                    cnf.append(clause)
                    # Diagonales sup
                    clause = [litterals[2 * diag_jj + 2 * i + 1], litterals[2 * diag_kk + 2 * i + 1]]
                    cnf.append(clause)
                    # Antidiagonales inf
                    clause = [litterals[2 * anti_diag_jj + 2 * i + 1], litterals[2 * anti_diag_kk + 2 * i + 1]]
                    cnf.append(clause)
                    # Antidiagonales sup
                    clause = [litterals[2 * anti_diag_jj - 2 * n * i + 1], litterals[2 * anti_diag_kk - 2 * n * i + 1]]
                    cnf.append(clause)
    return cnf


# Fonction qui permet de tester les solutions
def test_solution(problem, heuristic=None):
    P = DPLL(problem)
    P.resolve_1_solution(heuristic)
    for clause in range(P.n):
        cpt = True
        for variable in P.problem[clause]:
            if variable in P.etat_clauses:
                cpt = False
                break
        if cpt:
            return ('Houston we got a problem')
    return ('La solution fonctionne')


def lecture(position='', nom_fichier=''):
    file = open('problem.txt').read().split('\n')
    cnf = []
    for i in range(len(file)):
        clause = file[i].split(' ')

        clause_liste = []
        for j in range(len(clause)):
            lit = int(clause[j])
            clause_liste.append(lit)

        cnf.append(clause_liste)

    return cnf


def affichage_txt(position, nom_fichier=''):
    Fichier = lecture()
    cnf = Fichier[0]
    nb_lit = Fichier[-1]
    A = DPLL(cnf, nb_lit)
    A.resolve_all_solutions()
    filename = nom_fichier + '_Solution'
    file = open(filename, 'w')
    Sol = A.pile
    for elt in Sol:
        file.write(str(elt[0]) + ' : Vrai')
        file.write('\n')


###############################################################################
'Utilisation du code'

D = dames(9)

Dam_test = DPLL(D)
Dam_test.resolve_all_solutions(heuristic=1)

