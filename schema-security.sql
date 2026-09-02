-- Mejoras de seguridad - Resumen Lab (Sentry)
-- Correr una sola vez en el SQL Editor de Supabase del proyecto de esta app.

-- ---------------------------------------------------------------------
-- audit_log: trazabilidad basica de accesos y acciones sensibles
-- (login, logout, cambio de contrasena). El insert lo hace el propio
-- usuario logueado (con su JWT), nunca con la service_role key.
-- ---------------------------------------------------------------------
create table if not exists audit_log (
  id bigint generated always as identity primary key,
  actor_id uuid references auth.users(id) on delete set null,
  actor_username text,
  action text not null,
  detail text,
  created_at timestamptz not null default now()
);

create index if not exists audit_log_actor_idx on audit_log (actor_id);
create index if not exists audit_log_created_idx on audit_log (created_at desc);

alter table audit_log enable row level security;

-- Cualquier usuario logueado puede INSERTAR (dejar su propio registro),
-- pero nadie puede leer ni borrar desde el cliente: la lectura queda
-- reservada para quien entre directo a Supabase (o a un panel de admin
-- que se arme mas adelante usando la service_role key).
create policy "audit_log: usuario logueado inserta su propio evento"
  on audit_log for insert
  with check (auth.uid() = actor_id);

grant select, insert on public.audit_log to authenticated;

-- Trigger para completar actor_id/actor_username automaticamente asi el
-- frontend no tiene que mandarlos (evita que alguien inserte eventos a
-- nombre de otro usuario).
create or replace function audit_log_set_actor()
returns trigger
language plpgsql
security definer
as $$
begin
  -- Los inserts del frontend van con el JWT del usuario (auth.uid() presente):
  -- ahi pisamos actor_id/actor_username con lo real, para que nadie pueda
  -- mentir de quien fue la accion. Los inserts del script de ingesta usan la
  -- service_role key (auth.uid() es null) y ya mandan actor_username a mano
  -- (username de a quien se le aplico la accion) -- en ese caso lo respetamos.
  if auth.uid() is not null then
    new.actor_id := auth.uid();
    select username into new.actor_username from profiles where id = auth.uid();
  end if;
  return new;
end;
$$;

drop trigger if exists audit_log_set_actor_trigger on audit_log;
create trigger audit_log_set_actor_trigger
  before insert on audit_log
  for each row execute function audit_log_set_actor();

-- ---------------------------------------------------------------------
-- Password policy a nivel Supabase Auth (complementa la validacion del
-- frontend, que se puede saltear llamando a la API directo). Ir a:
-- Authentication > Policies > Password requirements, y configurar:
--   - Minimum length: 8
--   - Required characters: letras + numeros
-- Esto NO se puede hacer por SQL, es un ajuste del dashboard.
-- ---------------------------------------------------------------------
