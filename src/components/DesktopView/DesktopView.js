import React from "react";
import { ExplorerView, ExplorerIcon } from "packard-belle";
import { ProgramContext } from "../../contexts/programs";
import styles from "./_styles.scss";

const DesktopView = () => (
  <ProgramContext.Consumer>
    {context => (
      <ExplorerView className={styles.DesktopView}>
        {context.desktop.map(option => (
          <ExplorerIcon key={option.title} {...option} />
        ))}
      </ExplorerView>
    )}
  </ProgramContext.Consumer>
);

export default DesktopView;
