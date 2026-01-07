#![allow(unused_imports)]
#![allow(unused_variables)]
use k8s_openapi::api::core::v1::{Pod, PersistentVolumeClaim, PersistentVolume};
use std::time::{Duration, Instant};
use tokio::time::sleep;
use deps_hack::VStatefulSet;

use kube::{
    api::{Api, ListParams},
    Client, discovery::Discovery,
};
use tracing::*;
use crate::common::*;

pub fn v_statefulset() -> String {
    "
apiVersion: anvil.dev/v1
kind: VStatefulSet
metadata:
  name: pause-statefulset
  labels:
    app: stateful-demo
spec:
  replicas: 3
  serviceName: stateful-service
  selector:
    matchLabels:
      app: stateful-demo
  template:
    metadata:
      labels:
        app: stateful-demo
    spec:
      containers:
      - name: pause
        image: k8s.gcr.io/pause:3.9
  volumeClaimTemplates:
  - metadata:
      name: data
    spec:
      accessModes: [ \"ReadWriteOnce\" ]
      resources:
        requests:
          storage: 1Mi
"
    .to_string()
}

async fn wait_for_pods_for_vsts(client: Client, name: &str, expected: usize, timeout: Duration) -> Result<Vec<Pod>, Error> {
    let pod_api: Api<Pod> = Api::default_namespaced(client);
    let start = Instant::now();
    loop {
        if start.elapsed() > timeout {
            error!("Timeout waiting for pods for {}", name);
            return Err(Error::Timeout);
        }
        sleep(Duration::from_secs(3)).await;
        match pod_api.list(&ListParams::default()).await {
            Err(e) => {
                info!("List pods failed: {}", e);
                continue;
            }
            Ok(list) => {
                let pods: Vec<Pod> = list
                    .items
                    .into_iter()
                    .filter(|p| {
                        if let Some(n) = p.metadata.name.as_ref() {
                            n.starts_with(&format!("vstatefulset-{}-", name))
                        } else {
                            false
                        }
                    })
                    .collect();
                if pods.len() < expected {
                    info!("Have {} pods, want {}; still waiting.", pods.len(), expected);
                    continue;
                } else if pods.len() > expected {
                    info!("Have {} pods which is more than expected {}.", pods.len(), expected);
                    continue;
                } else {
                    info!("Found {} pods for VStatefulSet {}.", pods.len(), name);
                    return Ok(pods);
                }
            }
        }
    }
}

async fn check_pv_and_template(client: Client, vsts_name: &str, pods: &[Pod], timeout: Duration) -> Result<(), Error> {
    // pick first pod
    let first_pod = pods.get(0).ok_or(Error::VStatefulSetFailed)?;
    // find a PVC referenced by the pod
    let volumes = first_pod.spec.as_ref().map(|s| s.volumes.clone()).flatten().unwrap_or_default();
    let mut pvc_names = vec![];
    for v in volumes.iter() {
        if let Some(pvc) = v.persistent_volume_claim.as_ref() {
            pvc_names.push(pvc.claim_name.clone());
        }
    }
    if pvc_names.is_empty() {
        info!("No PVCs found for pod {}", first_pod.metadata.name.as_ref().unwrap());
        return Err(Error::VStatefulSetFailed);
    }

    let pvc_api: Api<PersistentVolumeClaim> = Api::default_namespaced(client.clone());
    let start = Instant::now();

    loop {
        if start.elapsed() > timeout {
            error!("Timeout waiting for PVCs to be bound for pod {}", first_pod.metadata.name.as_ref().unwrap());
            return Err(Error::Timeout);
        }
        // check if all PVCs are bound
        let mut all_bound = true;
        for claim in pvc_names.iter() {
            match pvc_api.get(claim).await {
                Err(e) => {
                    info!("Get PVC {} failed: {}", claim, e);
                    all_bound = false;
                    break;
                }
                Ok(pvc) => {
                    if pvc.status.as_ref().and_then(|s| s.phase.as_ref()).map(|s| s == "Bound").unwrap_or(false) {
                        info!("PVC {} is bound.", claim);
                        continue;
                    } else {
                        info!("PVC {} is not yet bound.", claim);
                        all_bound = false;
                        break;
                    }
                }
            }
        }
        if all_bound {
            info!("All PVCs are bound for pod {}", first_pod.metadata.name.as_ref().unwrap());
            break;
        }
        sleep(Duration::from_secs(3)).await;
    }
    // TODO: Add check on PV matching PVC later when we have VPV controller
    Ok(())
}

pub async fn vstatefulset_e2e_test() -> Result<(), Error> {
    let client = Client::try_default().await?;
    let discovery = Discovery::new(client.clone()).run().await?;
    let vsts_name = apply(v_statefulset(), client.clone(), &discovery).await?;

    let timeout = Duration::from_secs(20);
    // wait and check pods matching name against replicas
    let vsts_api: Api<VStatefulSet> = Api::default_namespaced(client.clone());
    let vsts = vsts_api.get(&vsts_name).await?;
    let replicas = vsts.spec.replicas.unwrap_or(1) as usize;
    let pods = wait_for_pods_for_vsts(client.clone(), &vsts_name, replicas, timeout).await?;

    // check PVs bound to first pod and compare one PV to pvc template
    check_pv_and_template(client.clone(), &vsts_name, &pods, timeout).await?;

    // scale up
    let new_replicas_up = replicas + 2;
    run_command(
        "kubectl",
        vec![
            "patch",
            "vsts",
            vsts_name.as_str(),
            "--type=json",
            "-p",
            &format!("[{{\"op\":\"replace\",\"path\":\"/spec/replicas\",\"value\":{}}}]", new_replicas_up),
        ],
        "failed to scale VStatefulSet up",
    );
    let _pods_up = wait_for_pods_for_vsts(client.clone(), &vsts_name, new_replicas_up, timeout).await?;

    // scale down
    let new_replicas_down = (replicas as isize - 1).max(1) as usize;
    run_command(
        "kubectl",
        vec![
            "patch",
            "vsts",
            vsts_name.as_str(),
            "--type=json",
            "-p",
            &format!("[{{\"op\":\"replace\",\"path\":\"/spec/replicas\",\"value\":{}}}]", new_replicas_down),
        ],
        "failed to scale VStatefulSet down",
    );

    // wait until pods with ordinal >= new_replicas_down are gone
    let pod_api: Api<Pod> = Api::default_namespaced(client.clone());
    let start = Instant::now();
    loop {
        if start.elapsed() > timeout {
            error!("Timeout waiting for scale down cleanup");
            return Err(Error::Timeout);
        }
        sleep(Duration::from_secs(3)).await;
        let list = pod_api.list(&ListParams::default()).await?;
        let mut found_bad = false;
        for p in list.items.iter() {
            if let Some(n) = p.metadata.name.as_ref() {
                if n.starts_with(&format!("vstatefulset-{}-", vsts_name)) {
                    // extract suffix after last '-'
                    if let Some(pos) = n.rfind('-') {
                        if let Ok(idx) = n[pos+1..].parse::<usize>() {
                            if idx >= new_replicas_down {
                                found_bad = true;
                                break;
                            }
                        }
                    }
                }
            }
        }
        if found_bad {
            info!("Found pods with ordinal >= {}; still waiting for deletion.", new_replicas_down);
            continue;
        }
        info!("Scale down cleanup verified.");
        break;
    }

    // TODO: fix spec check or find a workaround for getPodRevision
    // patch app version image and wait for pod with new image running
    // let new_image = "k8s.gcr.io/pause:3.10";
    // run_command(
    //     "kubectl",
    //     vec![
    //         "patch",
    //         "vsts",
    //         vsts_name.as_str(),
    //         "--type=json",
    //         "-p",
    //         &format!("[{{\"op\":\"replace\",\"path\":\"/spec/template/spec/containers/0/image\",\"value\":\"{}\"}}]", new_image),
    //     ],
    //     "failed to patch VStatefulSet image",
    // );

    // let start = Instant::now();
    // loop {
    //     if start.elapsed() > timeout {
    //         error!("Timeout waiting for image update");
    //         return Err(Error::Timeout);
    //     }
    //     sleep(Duration::from_secs(4)).await;
    //     let list = pod_api.list(&ListParams::default()).await?;
    //     let mut found = false;
    //     for p in list.items.iter() {
    //         if p.status.as_ref().and_then(|s| s.phase.as_ref()).map(|s| s == "Running").unwrap_or(false) {
    //             if let Some(spec) = p.spec.as_ref() {
    //                 if !spec.containers.is_empty() {
    //                     if let Some(img) = spec.containers.get(0).and_then(|c| c.image.as_ref()) {
    //                         if img == new_image {
    //                             info!("Found running pod {} with new image.", p.metadata.name.as_ref().unwrap());
    //                             found = true;
    //                             break;
    //                         }
    //                     }
    //                 }
    //             }
    //         }
    //     }
    //     if found {
    //         info!("Image update verified.");
    //         break;
    //     }
    // }

    info!("VStatefulSet e2e test passed.");
    Ok(())
}