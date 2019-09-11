SET citus.next_shard_id TO 20050000;

CREATE USER collationuser;
SELECT run_command_on_workers($$CREATE USER collationuser;$$);

CREATE SCHEMA collation_tests AUTHORIZATION collationuser;
CREATE SCHEMA collation_tests2 AUTHORIZATION collationuser;

SET search_path to collation_tests;

CREATE COLLATION case_insensitive (
	provider = icu,
	locale = 'und-u-ks-level2'
);

SET citus.enable_ddl_propagation TO off;

CREATE COLLATION case_insensitive_unpropagated (
	provider = icu,
	locale = 'und-u-ks-level2'
);

SET citus.enable_ddl_propagation TO on;

\c - - - :worker_1_port
SELECT c.collname, nsp.nspname, a.rolname
FROM pg_collation c
JOIN pg_namespace nsp ON nsp.oid = c.collnamespace
JOIN pg_authid a ON a.oid = c.collowner
WHERE collname like 'case_insensitive%'
ORDER BY 1,2,3;
\c - - - :master_port
SET search_path to collation_tests;

CREATE TABLE test_propagate(id int, t1 text COLLATE case_insensitive,
    t2 text COLLATE case_insensitive_unpropagated);
INSERT INTO test_propagate VALUES (1, 'a', 's'), (2, 'd', 'f');
SELECT create_distributed_table('test_propagate', 'id');

\c - - - :worker_1_port
SELECT c.collname, nsp.nspname, a.rolname
FROM pg_collation c
JOIN pg_namespace nsp ON nsp.oid = c.collnamespace
JOIN pg_authid a ON a.oid = c.collowner
WHERE collname like 'case_insensitive%'
ORDER BY 1,2,3;
\c - - - :master_port

ALTER COLLATION collation_tests.case_insensitive RENAME TO case_insensitive2;
ALTER COLLATION collation_tests.case_insensitive2 SET SCHEMA collation_tests2;
ALTER COLLATION collation_tests2.case_insensitive2 OWNER TO collationuser;

\c - - - :worker_1_port
SELECT c.collname, nsp.nspname, a.rolname
FROM pg_collation c
JOIN pg_namespace nsp ON nsp.oid = c.collnamespace
JOIN pg_authid a ON a.oid = c.collowner
WHERE collname like 'case_insensitive%'
ORDER BY 1,2,3;
\c - - - :master_port

SET client_min_messages TO error; -- suppress cascading objects dropping
DROP SCHEMA collation_tests CASCADE;
DROP SCHEMA collation_tests2 CASCADE;

DROP USER collationuser;
SELECT run_command_on_workers($$DROP USER collationuser;$$);
