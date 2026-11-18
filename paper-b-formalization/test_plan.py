"""Controls for the actual planning validator; these are not theorem tests."""
import copy
import unittest
import plan


class PlanControls(unittest.TestCase):
    def setUp(self):
        self.data, self.coverage, self.obligations, self.external = copy.deepcopy(plan.load())
        self.tasks = {t['id']: t for t in self.data['tasks']}

    def validate(self):
        return plan.validate_records(self.data, self.coverage, self.obligations, self.external)

    def test_valid_snapshot(self):
        self.validate()
        plan.validate_files(self.data, self.coverage)

    def test_unknown_dependency(self):
        self.tasks['EX1.1']['dependencies'].append('EX999.1')
        with self.assertRaisesRegex(plan.PlanError, 'unknown dependency EX999.1'):
            self.validate()

    def test_dependency_cycle(self):
        self.tasks['EX1.1']['dependencies'].append('EX5.4')
        with self.assertRaisesRegex(plan.PlanError, 'dependency cycle'):
            self.validate()

    def test_open_question_not_a_proof(self):
        q = next(e for e in self.coverage['entries'] if e['id'] == '6.2')
        q['tasks'] = ['EX6.2']
        with self.assertRaisesRegex(plan.PlanError, 'open question incorrectly assigned'):
            self.validate()

    def test_verified_label_without_evidence(self):
        t = self.tasks['EX0.1']
        t['status'], t['proof_status'] = 'VERIFIED', 'CERTIFIED'
        with self.assertRaisesRegex(plan.PlanError, 'verification record required'):
            self.validate()

    def test_one_writer_rule(self):
        self.tasks['EX2.4']['owner_role'] = 'resources'
        with self.assertRaisesRegex(plan.PlanError, 'module owner conflict'):
            self.validate()

    def test_uncovered_statement(self):
        for t in self.tasks.values():
            t['paper_consumers'] = [v for v in t['paper_consumers'] if v != '1.1']
        self.coverage['entries'][0]['tasks'] = []
        with self.assertRaisesRegex(plan.PlanError, 'uncovered paper statement'):
            self.validate()

    def test_premature_ready(self):
        self.tasks['EX1.1']['status'] = 'READY'
        with self.assertRaisesRegex(plan.PlanError, 'incomplete dependencies'):
            self.validate()

    def test_literal_statement_not_just_id(self):
        self.coverage['entries'][0]['statement'] += ' Changed claim.'
        with self.assertRaisesRegex(plan.PlanError, 'statement mismatch'):
            plan.validate_files(self.data, self.coverage)

    def test_module_import_cycle(self):
        graph = copy.deepcopy(plan.read_json(plan.ROOT / 'module-graph.json'))
        kernel = next(m for m in graph['modules'] if m['path'].endswith('/Index.lean'))
        kernel['local_imports'].append('release-core/Solution.lean')
        with self.assertRaisesRegex(plan.PlanError, 'local module import cycle'):
            plan.validate_module_graph(self.data, graph)

    def test_challenge_cannot_import_project(self):
        graph = copy.deepcopy(plan.read_json(plan.ROOT / 'module-graph.json'))
        graph['modules'][0]['local_imports'].append('release-core/PaperB/Spec.lean')
        with self.assertRaisesRegex(plan.PlanError, 'Challenge has project import'):
            plan.validate_module_graph(self.data, graph)

    def test_unreachable_release_module(self):
        graph = copy.deepcopy(plan.read_json(plan.ROOT / 'module-graph.json'))
        path = 'release-core/PaperB/Unused.lean'
        graph['modules'].append({'path':path,'local_imports':[],'owner_role':'graph','admission':'ORACLE_CORE'})
        self.data['module_owners'][path] = 'graph'
        with self.assertRaisesRegex(plan.PlanError, 'unreachable planned first-release module'):
            plan.validate_module_graph(self.data, graph)

    def test_root_count_cannot_be_inflated(self):
        self.data['formal_roots_accepted'] = 1
        with self.assertRaisesRegex(plan.PlanError, 'certified root count'):
            self.validate()

    def test_missing_new_corollary(self):
        self.coverage['entries'] = [e for e in self.coverage['entries'] if e['id'] != '1.2']
        with self.assertRaisesRegex(plan.PlanError, 'wrong active manuscript inventory size'):
            self.validate()

    def test_unsupported_extension_closure(self):
        self.obligations['extension_obligations'][0]['status'] = 'CLOSED'
        with self.assertRaisesRegex(plan.PlanError, 'unsupported extension closure'):
            self.validate()

    def test_tracker_active_source_identity(self):
        self.data['manuscript']['sha256'] = '0' * 64
        with self.assertRaisesRegex(plan.PlanError, 'tracker active-source identity mismatch'):
            plan.validate_files(self.data, self.coverage)

    def test_deferred_proof_cannot_use_corollary_proof(self):
        theorem, corollary = self.coverage['entries'][:2]
        self.assertGreater(theorem['proof_source_line'], corollary['proof_source_line'])
        theorem['proof_sha256'] = corollary['proof_sha256']
        with self.assertRaisesRegex(plan.PlanError, '1.1: proof binding mismatch'):
            plan.validate_files(self.data, self.coverage)

    def test_proof_marker_must_be_unique(self):
        source = (plan.ROOT / 'sources/paper-b-v1.2-draft.md').read_text()
        source += '\n*Proof of Theorem 1.1.* Duplicate. ∎'
        with self.assertRaisesRegex(plan.PlanError, 'ambiguous deferred proof'):
            plan.statement_proof(source, plan.PATTERN.search(source))

    def test_proof_cannot_cross_another_statement(self):
        source = '**Lemma 2.1 (one).** Claim.\n\n*Proof.* Missing end.\n\n**Lemma 2.2 (two).** Claim.\n\n*Proof.* Done. ∎'
        with self.assertRaisesRegex(plan.PlanError, 'incomplete proof'):
            plan.statement_proof(source, plan.PATTERN.search(source))

    def test_threshold_is_no_longer_a_selected_root(self):
        self.obligations['obligations'][0]['paper_root'] = '3.2'
        with self.assertRaisesRegex(plan.PlanError, 'incorrect selected roots'):
            self.validate()

    def test_certification_cannot_bypass_root_obligations(self):
        self.coverage['entries'][0]['formal_status'] = 'CERTIFIED'
        with self.assertRaisesRegex(plan.PlanError, 'certification without verified tasks'):
            self.validate()

    def test_obligation_must_have_the_right_consumer(self):
        self.obligations['obligations'][0]['tasks'] = ['EX6.2']
        with self.assertRaisesRegex(plan.PlanError, 'unknown obligation task'):
            self.validate()

    def test_duplicate_task_id(self):
        self.data['tasks'].append(self.data['tasks'][0])
        with self.assertRaisesRegex(plan.PlanError, 'duplicate task ID'):
            self.validate()

    def test_open_question_has_no_proof_digest(self):
        question = self.coverage['entries'][-1]
        question['proof_sha256'] = '0' * 64
        with self.assertRaisesRegex(plan.PlanError, '6.2: proof binding mismatch'):
            plan.validate_files(self.data, self.coverage)


if __name__ == '__main__':
    unittest.main(verbosity=2)
