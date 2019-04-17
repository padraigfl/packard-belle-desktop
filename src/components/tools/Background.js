import React from "react";
import cx from "classnames";

import styles from "./_background.scss";
import { SettingsContext } from "../../contexts/settings";

const Background = props => (
  <SettingsContext.Consumer>
    {context =>
      context.bgImg ? (
        <div
          className={cx(styles.Background, {
            [styles["Background--tiled"]]: context.bgStyle === "tile",
            [styles["Background--contain"]]: context.bgStyle === "contain",
            [styles["Background--stretch"]]: context.bgStyle === "stretch"
          })}
        >
          <div style={{ backgroundImage: `url(${context.bgImg})` }} />
        </div>
      ) : null
    }
  </SettingsContext.Consumer>
);
export default Background;
